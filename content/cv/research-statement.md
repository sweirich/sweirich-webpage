Research
========

TRELLYS
-------

The TRELLYS project seeks to design a dependently-typed
programming language that supports both programming and theorem proving
in the same framework. With [Aaron
Stump](http://homepage.cs.uiowa.edu/%7Eastump/) (Iowa State) and [Tim
Sheard](http://web.cecs.pdx.edu/%7Esheard/) (Portland State), we have
been discovering what it means for programs and proofs to interact. See
our recent [paper submission](papers/modal.pdf), as well as papers in
[MSFP](http://www.seas.upenn.edu/%7Esweirich/papers/msfp12log.pdf)
[2012](http://www.seas.upenn.edu/%7Esweirich/papers/msfp12prog.pdf) and
[PLPV
2012](http://www.seas.upenn.edu/%7Esweirich/papers/plpv2012genreccbv.pdf).
Also, slides from [PLPV 2010](talks/TrellysPLPV.pdf) and [RDP
2011](talks/tlca-2011.pdf), give an overview of our work. 


Dependently-Typed Haskell
-------------------------

 Working with [Simon Peyton
Jones](http://research.microsoft.com/en-us/people/simonpj/) and [Dimitrios
Vytiniotis](http://research.microsoft.com/en-us/people/dimitris/) at MSR
Cambridge, Penn students Brent Yorgey, Richard Eisenberg and Justin Hsu and I
have been working to extend the type system of Haskell with better support for
dependently-typed programing. \

-   [Down with kinds: adding dependent heterogenous equality to
    FC](papers/nokinds-extended.pdf) (in submission) extends GHC's core
    language with support for kind equalities.\
-   [Dependently-typed programming with
    singletons](http://www.cis.upenn.edu/%7Eeir/papers/2012/singletons/paper.pdf)
    (Haskell Symposium 2012) discusses the
    [singletons](http://hackage.haskell.org/package/singletons) library
    that automatically generates infrastructure for dependently-typed
    programming.\
-   [Giving Haskell a Promotion](papers/tldi12.pdf) (TLDI 2012, with
    [Jos Pedro Maglhaes](http://dreixel.net/) and [Julien
    Cretin](http://gallium.inria.fr/%7Ejcretin/)) adds kind polymorphism
    and datatype promotion to GHC.

Type-directed programming
------------------------

Defining functions via type information cuts down on boilerplate programming
as many operations may be defined once, for all types of data. With my student
[Brent Yorgey](http://www.cis.upenn.edu/%7Ebyorgey/) and collaborator [Tim
Sheard](http://web.cecs.pdx.edu/%7Esheard/) (Portland State), I developed
[Unbound](http://hackage.haskell.org/package/unbound/), a
[Haskell](http://www.haskell.org/ghc/) library for declaratively specifying
binding structure and automatically generating free variable,
alpha-equivalence and substitution functions. This library is built using
[RepLib](http://hackage.haskell.org/package/RepLib/), an expressive library
that I developed for generic programming in Haskell. My student [Chris
Casinghino](http://www.seas.upenn.edu/%7Eccasin/)and I explored [arity and
type generic programming in
Agda](http://www.seas.upenn.edu/%7Esweirich/papers/aritygen.pdf), [lecture
notes](http://www.seas.upenn.edu/%7Esweirich/ssgip/) from the[Spring School on
Generic and Indexed
Programming](http://www.comlab.ox.ac.uk/projects/gip/school.html) provide a
gentle introduction.\
     

Machine assistance for programming languages research
------------------------------------------------------

Designing and proving properties about programming languages is hard, but the
proofs themselves are straightforward once you know how to set them up. At the
same time, it is all too easy to miss the one little case that ruins the whole
"proof". Modern proof assistants, such as
[Twelf](http://www.cs.cmu.edu/%7Etwelf/), [Coq](http://coq.inria.fr/), and
[Isabelle](http://www.cl.cam.ac.uk/Research/HVG/Isabelle/) are good at
expressing this sort of reasoning, but it is hard to know where to start. I've
been working with the [POPLmark
team](http://www.cis.upenn.edu/proj/plclub/mmm/) to issue [challenge
problems](http://www.cis.upenn.edu/proj/plclub/mmm/), organize a
[workshop](http://www.seas.upenn.edu/%7Esweirich/wmm/), explore [techniques
for reasoning about
binding](http://www.seas.upenn.edu/%7Esweirich/papers/nominal-coq/), and
develop [educational
materials](http://www.seas.upenn.edu/%7Esweirich/cis700/f06/) about
mechanizing programming language metatheory. Brian Aydemir developed a
[library](http://www.cis.upenn.edu/%7Eplclub/metalib/) for programming
language metatheory (used in the Penn tutorials) and
[LNgen](http://www.cis.upenn.edu/%7Ebaydemir/papers/lngen/), a tool for
automatically proving properties about binding.\

Type inference for advanced type systems
---------------------------------------- 

Advanced type system features, such as [first-class
polymorphism](papers/putting.pdf), [impredicative
polymorphism](http://www.seas.upenn.edu/%7Esweirich/papers/icfp08.pdf) and
[generalized algebraic
datatypes](http://www.seas.upenn.edu/%7Esweirich/papers/gadt.pdf), do not
interact well with the standard algorithms for type inference in modern typed
functional languages, such as ML and Haskell.   [Simon Peyton
Jones](http://research.microsoft.com/%7Esimonpj/), my students Dimitrios
Vytiniotis, Geoffrey Washburn and I have incorporated ideas from Local Type
Inference to extend the [Glasgow Haskell
Compiler](http://www.haskell.org/ghc/) with support for these features. \

Combinatorial Species
---------------------

