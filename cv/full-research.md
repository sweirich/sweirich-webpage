Research Statement
==================

Motivation
----------

The goal of my research is to enhance the reliability, maintainability, and
security of software systems through programming language technology.  The
design of programming languages strongly determines the properties of programs
written in them. A good language will promote the design of trustworthy and
robust software and discourage the creation of insecure and inflexible code.

In pursuit of this goal, my research focuses on the design of
*statically-typed programming languages.* Static type systems are a popular,
cost-effective form of lightweight program verification.  They provide a
tractable and modular way for programmers to express properties that can be
mechanically checked by the compiler, thereby ruling out a wide variety of
common memory manipulation and control-flow errors. For example, systems
written with type-safe languages cannot be compromised by buffer overruns if
all array accesses are statically proven safe. In general, the value of a
static type system rests in its ability to express the invariants and
consistency properties of software systems.

However, the static type systems of modern programming languages are limited
in their expressiveness. Some programming idioms must be ruled out simply
because they cannot be shown to be sound by a particular type system.  My
research explores novel methods to bring more expressive types systems to
users: enhancing the capabilities of existing type systems to reason about
run-time structure and behavior, reconciling the features of
expressive-but-theoretical type systems with existing languages, partially
automating the process of type system design so that we may be more confident
in the soundness of more complicated type systems, and incorporating
programming logics into the design of practical type systems so that
application-specific properties may be expressed.

Below, I describe this research in more detail as well as my future
directions.

Semantics and Design of Dependently-typed Languages
---------------------------------------------------

While extremely helpful for building robust software, the type systems used in
practice verify only relatively weak safety properties; they fall far short of
what is needed to do full verification of program correctness. This
inexpressiveness is partly by design---full program verification is
potentially expensive, not fully automatable, and probably unwarranted for
non-safety-critical software. Nevertheless, there are many situations in which
the ability to specify program properties richer than current type systems
permit would be useful. In fact, there is a spectrum of possibilities between
simple type safety and full program verification.

Dependent type systems extend the type systems of current practice to allow
incremental, lightweight specifications. They work by allowing types that are
used as specifications to depend on values computed by program
expressions. However, even though the theory behind dependent type systems has
been refined over several decades, such type systems have been little used in
practical programming languages. 

The **Trellys project**, a joint project between my group at Penn, and groups
at the University of Iowa and Portland State University, investigated the
design and implementation of a programming language with dependent types,
called Trellys.  Trellys is the only research group addressing issues in the
design of a call-by-value, full spectrum dependently-typed language.

1. An investigation of the semantics of equality in a call-by-value language
 with nontermination and dependent-types
 [@casinghino:combining-proofs-programs;@pii13kimmel;@teqt;@iseq].

2. Practical considerations for a dependently-typed language, including type 
inference [@sjoberg:congruence] and computational irrelevance [@sjoberg:msfp12].

I've also work to build the community of researchers that study the
interaction between dependent types and functional programming. In particular,
I organized two meetings: the DTP workshop co-located with ICFP 2013, and the
Shonan Seminar 007 in 2011.

This work has been recognized through invitations for keynote addresses (PLMW
2014, RTA 2011, MFPS 2011), lectures at the OPLSS summer school (2014 and
2013), and discussion sessions at the PLPV workshop (2011 and 2010).


Extending the Haskell Type System
---------------------------------

The Haskell programming language has been dramatically growing in popularity
in the past five years. Part of this growth can be attributed to its
"incredibly expressive static type system."

Haskell has one of the world's most advanced type systems. Because of the
 advantage that this type system brings


For the past ten years, I have been working with Simon Peyton Jones, Dimitrios
Vytiniotis and many others on extensions to the type system of the Glasgow
Haskell Compiler. In that space, I've contributed to several extensions to
both the source and core languages,  and Roles.

1. Language extensions for dependently-typed programming in GHC

Generalized Algebraic Datatypes
[@pj-vytiniotis:wobbly], Kind polymorphism and datatype
promotion [@weirich:dwk;@weirich:lifting], Type families[@eisenberg:closed-tf].

2. Haskell libraries
   The singletons library (used by the units library for physical simulation). 
	The RepLib library (used by the Unbound library for modeling variable binding).

3. Modularity and notions of type equality [@coercions;@roles]

4. First-class polymorphism []

This work has been recognized through invitations for keynote addresses (ICFP
2014, FLOPS 2012) and chairing of ICFP 2010 and Haskell Symposium 2009.

Member of IFIP WG 2.8


Mechanizing programming language metatheory
-------------------------------------------

Because program security guarantees are often based on static type
checking, confidence in the soundness of static type systems is
essential. Yet, as static type systems become more and more
expressive, such meta-theoretic results become more complex.
Typically proofs about the properties of programming languages are
done by hand, despite the length and complexity of these results for
modern languages. These proofs are not difficult---they use standard,
well-understood techniques---but they are often overwhelming in the
details. 

Therefore, I have been working to make the use of automated proof
assistants more commonplace in the formalization of programming
language metatheory. This project has two components: developing
community infrastructure (education materials, workshops, libraries,
electronic fora) to get researchers to use existing tools, and
developing new technologies for programming language representation,
specifically, the treatment of binding constructs, to make this
process easier.

I have been working on this project in collaboration with Benjamin Pierce and
Steve Zdancewic at the University of Pennsylvania as well as Peter Sewell at
Cambridge University and Randy Pollack at the University of Edinburgh and a
number of Penn students.  This project was supported by the NSF CISE Computing
Research Infrastructure program and the DARPA Computer Science Study Group.

1. POPLmark challenge and educational infrastructure

In 2005, the POPLmark team issued the POPLmark challenge: a set of design
problems to both assess and advance the current best practices in
machine-assisted support for the formalization of programming languages.  This
challenge was met with enthusiasm and spurred vigorous debate. Benjamin Pierce
and I co-edited a [journal special issue](jar) devoted to descriptions of the
POPLmark challenge. I was invited to give retrospective talks at Cambridge
University (Dec 2009) and LFMTP 2012.

Based on this initial success, I organized and chaired the 2006 Workshop on
Mechanizing Metatheory, which was held in conjunction with ICFP, and attended
by over fifty participants. This workshop had additional meetings in 2007,
2008, 2009, and 2010. Furthermore, we organized a tutorial on using Coq for
programming language metatheory at POPL 2008 and I repeated this tutorial at
OPLSS 2008.

2. Binding representations and tools

LNgen

Penn library

References 
==========

