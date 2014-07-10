(* Major edits by Brian Aydemir (baydemir [at] cis.upenn.edu).

   Not much of the original version remains.  It is assumed that
   theorems are not nested inside each other and that they are not
   proved via "Proof <proof term>.".  Blank lines within proof scripts
   are not counted.  Comments are ignored for the purposes of counting
   lines. *)

(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* coqwc - counts the lines of spec, proof and comments in Coq sources
 * Copyright (C) 2003 Jean-Christophe Filliâtre *)

(*i $Id: coqwc.mll 9691 2007-03-08 15:29:27Z msozeau $ i*)

(*i*){
open Printf
open Lexing
open Filename
(*i*)

let debug str =
  print_string str;
  flush stdout

let spec_lines = ref 0
let proof_lines = ref 0
let theorems = ref 0

let reset_counters () =
  spec_lines := 0;
  proof_lines := 0;
  theorems := 0

let incr counter =
  match counter with
    | Some c -> c := !c + 1
    | None -> ()

let print_line spec proof theorems file =
  printf " %8d" spec;
  printf " %8d" proof;
  printf " %8d" (spec + proof);
  printf " %8d" theorems;
  (match file with Some f -> printf " %s" f | _ -> ());
  print_newline ()

let print_file file = print_line !spec_lines !proof_lines !theorems file

(*i*)}(*i*)

(* Assume that the space(s) after a dot don't need to be accounted for
   in line counts. *)

let space = [' ' '\r' '\t' '\n']
let dot = '.' (space+ eof? | eof)

(* The start of a possibly interactive definition. *)

let def_start =
  "Definition"

(* The start of any other specification. *)

let spec_start =
  "Axiom" | "Hypothesis" | "Hypotheses" |
  ("Parameter" "s"?) | ("Variable" "s"?) |
  "Fixpoint" | "Inductive" | "Module" | "Section" | "End"

(* The start of a theorem. *)

let thm_start =
  "Theorem" | "Lemma" | "Fact" | "Remark" | "Goal" |
  "Correctness" | "Obligation" | "Next"

(* The end of a proof. *)

let proof_end =
  ("Save" | "Qed" | "Defined" | "Abort" | "Admitted") [^'.']* dot

(* General algorithm:
   - Look for the beginning of something interesting.
   - Increment the appropriate counter.
   - Dispatch to a handler specific for that something.
   - The handler is responsible for incrementing the
     appropriate counter whenever it encounters a newline character.
*)

(* Entry point into the lexer.  We look for the start of something
   interesting and dispatch to the appropriate handler. *)

rule main = parse
  | eof
      { () }
  | space+
      (* consume whitespace *)
      { main lexbuf }
  | "(*"
      (* beginning of comment *)
      { comment lexbuf; main lexbuf }
  | thm_start
      (* theorem *)
      { incr (Some spec_lines);
        incr (Some theorems);
        skip_to_dot (Some spec_lines) lexbuf;
        incr (Some proof_lines);
        proof false lexbuf;
        main lexbuf
      }
  | spec_start
      (* specification *)
      { incr (Some spec_lines);
        skip_to_dot (Some spec_lines) lexbuf;
        main lexbuf
      }
  | def_start
      (* definition *)
      { incr (Some spec_lines);
        definition true lexbuf;
        main lexbuf
      }
  | _
      (* unknown entity; ignore it *)
      { skip_to_dot None lexbuf; main lexbuf }

(* Process a definition, being careful to determine whether it is
   interactively given or not.  Recommended default: Assume that a
   proof follows. *)

and definition goto_proof = parse
  | eof
      { () }
  | "(*"
      { comment lexbuf; definition goto_proof lexbuf }
  | '"'
      { string (Some spec_lines) lexbuf; definition goto_proof lexbuf }
  | '\n'
      { incr (Some spec_lines); definition goto_proof lexbuf }
  | ":="
      { definition false lexbuf }
  | dot
      { if goto_proof then begin
          incr (Some proof_lines); proof false lexbuf
        end else
          main lexbuf
      }
  | _
      { definition goto_proof lexbuf }

(* Process a proof.  The flag indicates whether we've seen a
   non-whitespace character on the current line.  Recommended default:
   false. *)

and proof seen_nonwhitespace = parse
  | proof_end
      { () }
  | '"'
      { string (Some proof_lines) lexbuf; proof true lexbuf }
  | "(*"
      { comment lexbuf; proof seen_nonwhitespace lexbuf }
  | '\n'
      { if seen_nonwhitespace then
          incr (Some proof_lines);
        proof false lexbuf
      }
  | eof
      { () }
  | [' ' '\t']
      { proof false lexbuf }
  | _
      { proof true lexbuf }

(* Consume characters up to the next dot.  Increment the (optionally)
   supplied counter upon each newline character encountered. *)

and skip_to_dot counter = parse
  | dot
      (* dot encountered *)
      { () }
  | '"'
      { string counter lexbuf; skip_to_dot counter lexbuf }
  | "(*"
      { comment lexbuf; skip_to_dot counter lexbuf }
  | '\n'
      { incr counter; skip_to_dot counter lexbuf }
  | eof
      { () }
  | _
      { skip_to_dot counter lexbuf }

(* Finish scanning a comment.  Assumes that the opening "(*" has
   already been consumed.  Comments count for nothing, as far as line
   counts are concerned. *)

and comment = parse
  | "(*"
      { comment lexbuf; comment lexbuf }
  | "*)"
      { () }
  | '"'
      { string None lexbuf; comment lexbuf }
  | eof
      { () }
  | _
      { comment lexbuf }

(* Finish scanning a string.  Assumes that the opening doublequote has
   already been consumed.  Increment the (optionally) supplied counter
   upon each newline character encountered. *)

and string counter = parse
  | '"'
      (* end of string *)
      { () }
  | '\\' _
      (* escaped character *)
      { string counter lexbuf }
  | '\n'
      (* new line *)
      { incr counter; string counter lexbuf }
  | eof
      { () }
  | _
      { string counter lexbuf }

(*i*){(*i*)

(*s Processing files and channels. *)

let process_channel ch =
  let lb = Lexing.from_channel ch in
    reset_counters ();
    main lb

let process_file f =
  try
    let ch = open_in f in
    process_channel ch;
    close_in ch;
    print_file (Some f)
  with
    | Sys_error "Is a directory" ->
        flush stdout; eprintf "coqwc: %s: Is a directory\n" f; flush stderr
    | Sys_error s ->
        flush stdout; eprintf "coqwc: %s\n" s; flush stderr

(*s Parsing of the command line. *)

let usage () =
  prerr_endline "usage: coqwc [files]";
  exit 1

let rec parse = function
  | [] -> []
  | ("-h" | "-?" | "-help" | "--help") :: _ -> usage ()
  | f :: args -> f :: (parse args)

(*s Main program. *)

let main () =
  let files = parse (List.tl (Array.to_list Sys.argv)) in
    printf "     spec    proof    total     thms\n";
    match files with
      | [] -> process_channel stdin; print_file None
      | [f] -> process_file f
      | _ -> List.iter process_file files

let _ = Printexc.catch main ()

(*i*)}(*i*)
