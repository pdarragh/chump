---
documentclass: acmart
classoption: acmlarge,screen
title: "CHUMP: A Mechanically Verified Implementation of Curricle"
subtitle: "CMSC 838L --- Final Project Report"
author:
- name: Justin Frank
  email: jpfrank@umd.edu
  affiliation:
    institution: University of Maryland
    city: College Park
    state: MD
    country: USA
- name: Pierce Darragh
  email: pdarragh@umd.edu
  affiliation:
    institution: University of Maryland
    city: College Park
    state: MD
    country: USA
indent: true
bibliography: report.bib
header-includes: |
  \usepackage[utf8]{inputenc}
  \usepackage{syntax}
  \usepackage{float}
  \setcopyright{none}
  \acmVolume{3}
  \acmNumber{1}
  \acmArticle{1}
  \acmBooktitle{Proceedings of the First Occurrence of CMSC 838L}
include-before: |
numbersections: true
---

Curricle is an existing work that resolves some constraints in the
implementation of systems for batteryless energy-harvesting devices. The
approach develops a new type system that encodes a first-class notion of
idempotence that, when combined with inferred information about
input-taintedness and memory usage patterns, can guarantee a notion of safety
for these systems by ensuring certain variables are checkpointed at appropriate
points. The authors argue that this type-system-based approach strikes a balance
between ease of use for programmers and reduced checkpointing overhead.

However, the theoretical underpinnings of Curricle are incredibly complex,
consuming nearly 50 pages of semantic diagrams and proofs in the extended form
of the publication. Believing in the claims of the authors but wanting to lend
credibility to the theory of the system, we seek to mechanically verify Curricle
in Rocq (formerly Coq). Unfortunately, this report details an as-yet-incomplete
attempt at accomplishing this goal. This is due in large part to the fundamental
difficulty of mechanical verification, but it may also be the case that the
authors' choices early in the project development negatively impacted the
long-term outcomes. We investigate these shortcomings and reflect on the current
status and potential future of this work.


# Introduction

Curricle [@Curricle] attempts to solve a common problem in the design space of
programs for batteryless energy-harvesting devices (EHDs). EHDs have the
property that they might turn off at any time during execution, which normally
leads to the loss of necessary information in the course of computing something.
To solve this, EHDs typically feature both volatile and non-volatile memory that
programmers can use to save information across power failures. EHD systems are
deployed with mechanisms for restoring the last-active memory state so they can
resume execution.

One of the biggest hurdles in the use of such systems is the burden placed on
programmers to correctly maintain their invariants. Various infrastructures have
been developed in service of this goal, one category of which is
\emph{checkpointing}. In a checkpointing system, variables are marked for saving
at specific points, meaning their information will be stored in non-volatile
memory. Upon restoring from a power failure, the EHD will resume the program and
the checkpointing system will restore the values of the checkpointed variables,
resuming its execution from the last completed checkpoint.

However, the designers of the checkpointing systems have to balance ease of use
with performance. The system could be made to automatically save all variables
at each checkpoint, such that the programmer need only specify the checkpoint
locations, but this incurs significant performance overhead in terms of both
speed and power consumption. On the other hand, the system could leave the
choice of which variables to checkpoint to the programmer and do nothing
automatically, but this places an enormous burden on the programmer and is prone
to failure (e.g., the programmer may forget to checkpoint an important
variable).

Curricle provides a type-system-based approach to resolving this problem.
Instead of requiring the programmer to checkpoint variables manually, they need
only specify which variables are non-idempotent and set the checkpoints. From
there, Curricle checks that the program is consistent with respect to the
idempotence restrictions and checkpoint locations. The end result is a program
that does not checkpoint more than needed while reducing the burden on the
programmer. In addition, moving these concerns into the type system means
programs that are not consistent will be rejected up-front, signaling to the
programmer what they need to correct.

We found Curricle to be an impressive development, but a look through the full
technical report reveals the system to be incredibly complex. Complex systems
are often difficult to re-implement and can also contain subtle bugs. In service
of improving the reliability of Curricle, we set out to mechanically verify the
system using the Rocq theorem prover. However, because we found ourselves
subjected to external time constraints and due to our lack of experience in
mechanical verification, we removed some complexity from the type system to make
the problem more tractable. Despite these simplifications, we experienced no
shortage of setbacks and were unable to meet our goals.

In this report, we:

  * Explain the simplified system.
  * Discuss challenges that prohibited successful development of the system.
  * Describe the character of the proofs we wish to develop.
  * Evaluate the current implementation.
  * Make a plan for future work.


# CHUMP {#sec:chump}

The system supported by Curricle is built on top of Rust. This is useful to
programmers because it makes the system easier to use, since it does not require
a particularly strange toolchain. However, Rust features a complex memory use
analysis as part of its type system. While this is a significant boon in favor
of Rust's adoption as a low-level systems language (and a bonus for Curricle),
it significantly complicates the development of proofs --- mechanical or
otherwise --- that use it.

The extended Curricle report (see \ref{sec:extended}) contains dozens of pages
of semantics and proofs, and a not-insignificant portion of these is due, at
least in part, to the underlying complexity of Rust's type system. The Curricle
authors' choice to include this in their formalization is reasonable given the
intended use case, but the complexity of the proofs was a significant cause for
concern for these authors. We set about developing a new, smaller language
primarily intended to reduce the complexity of the proofs we would later
develop.


## Syntax

\begin{figure}
\centering
\begin{minipage}[t]{0.45\textwidth}
\begin{grammar}
<c> ::= let <x> := <e> in <c>
   \alt let <x> := INPUT in <c>
   \alt if <e> <c> <c>
   \alt noop
   \alt loop <c>
   \alt break <n>
   \alt <c> ; <c>
   \alt checkpoint
\end{grammar}
\end{minipage}
\begin{minipage}[t]{0.45\textwidth}
\begin{grammar}
<e> ::= <n> | <b>
   \alt <e> <op2> <e>

<op2> ::= + | -- | $\times$

<v> ::= <n> | <b>

<x> ::= <var>
\end{grammar}
\end{minipage}
\caption{The abstract syntax of CHUMP.}
\label{grammar}
\end{figure}

Figure \ref{grammar} shows the abstract syntax of CHUMP, our significantly
reduced language. In contrast to the language supported by Curricle, CHUMP does
away with functions, structs, and pointer expressions of any kind. We also
generalize loops, providing an indexed `break` command to terminate execution
(which can be nested within conditional `if` forms to simulate `while`-loop
behavior). Our hope in cutting out so many features was to greatly simplify the
mechanization of the system.

## Semantic Model

\begin{figure}
\begin{verbatim}
Definition env        := list loc.
Record     store      := mkStore { st_next : positive; st_map : pmap loc }.
Inductive  kont       := kMt | kSeq (c2 : cmd) (E : env) (k : kont).
Definition checkpoint := kont * list (loc * val).
Definition CESKP      := cmd * env * store * kont * checkpoint.
\end{verbatim}
\caption{The definitions of the E, S, K, and P of our CESKP machine.}
\label{eskp}
\end{figure}

To model the semantics, we use a derivation of the CESK style. The choice of a
CESK-based semantics was primarily due to the authors being familiar with this
style, as well as a belief that such a style would be easier to mechanize
compared to others. A CESK-style abstract machine features four components:

  1. **C**ontrol --- What to do next.
  2. **E**nvironment --- A map of variables to addresses.
  3. **S**tore --- A map of addresses to values.
  4. **K**ontinuation --- A context tracking what to do later.

In addition to these traditional elements, we add a fifth:

  5. Check**P**oint --- A safe state to restore to after reboot.

This gives us a CESK**P** machine. Figure \ref{eskp} shows the Rocq definitions
of the E, S, K, and P components.

In our model, we have only two varieties of continuation: the empty
continuation, denoted `kMt`, and the sequencing continuation, `kSeq`. The `kSeq`
continuation saves a second command, an environment, and another continuation.
The second command is just what needs to be done after the first command in the
sequence is fully executed. The environment is saved at the point at which the
sequence is invoked, i.e., it contains only the variables that are visible to
_both_ commands in the sequence. Lastly, the nested continuation is needed to
model complex control flow.

A checkpoint is a pair consisting of a continuation and a list of
location--value pairs. The continuation represents what was left to be done in
the program at the point at which the checkpoint was invoked, while the
location--value pairs constitute a partial store to be restored upon reboot.
These are the values of the checkpointed variables as they existed when the
checkpoint was passed. As noted previously, continuations in our model contain
environments, so the continuation with this partial store are enough information
to restore the state of the machine as expected.


## Input and Output

\begin{figure}
\caption{The definitions of the IO events and log.}
\label{io-log}
\begin{verbatim}
Variant io_event  := io_in  (i : Z)
                   | io_out (i : Z)
                   | io_check
                   | io_reset.

Definition io_log := list io_event.

Definition state  := CESKP * io_log.
\end{verbatim}
\end{figure}

We chose to separate the notions of input and output from the CESKP abstract
machine. This is a deviation from Curricle: Curricle's authors chose to consider
"output" to be "the observable state of memory at the end of execution". We
instead develop a distinct IO event log. This decision was arrived at after some
consideration of what might be easiest to mechanically verify. Separating IO
from the base abstract machine means we can develop a theory of the abstract
machine on its own, and later encapsulate it within a broader context including
the IO formalization. Figure \ref{io-log} shows the definitions.


## Simplified Checkpointing

Curricle supports multiple notions of checkpointing. Specifically, the authors
support both JIT- and atomic-region-based views on checkpoint semantics, and
the system is agnostic to the specific checkpoint implementation (e.g., undo vs.
redo checkpointing). These axes of choice provide great flexibility for
real-world systems, especially for a domain as varied as intermittent computing
that employs devices and systems of all kinds.

However, complexity is the enemy of mechanized verification, so we stripped it
down significantly.

Our semantics are built to handle only undo checkpointing, and we implicitly
define all code as existing within atomic regions between checkpoints. Narrowing
down the options in this manner gives a much smaller system, and was hoped to
simplify the proof of the system later on. Currently, we have concerns that this
choice in simplification may actually have caused unexpected complication: the
way we structured our syntax and checkpoint system suggests that checkpoints can
be _conditional_. This is atypical, and may end up causing more problems than it
is worth. The authors cross their fingers for a happy outcome, but we do not
hold our collective breath.


# Challenges Encountered {#sec:challenges}

In the process of implementing this work, we experienced a number of challenges,
many of which we have unfortunately not yet overcome.


## Lack of Deep Comprehension {#sec:extended}

When we began our effort to mechanically verify Curricle, we felt that we had a
reasonable understanding of the system and how we would go about proving its
correctness, and we thought that we could make significant headway with what we
knew then. Yet as we got into the minutiae of the actual implementation, we
found that our comprehension was actually quite shallow, and this proved to be a
significant setback in accomplishing much of anything.

We discovered the existence of an extended version of the Curricle paper,
complete with many pages of semantics and proofs to explain the system in depth
(which has been mentioned elsewhere, but its discovery originated here). Reading
this extended paper allowed us to fill in the gaps in our knowledge, but
unfortunately it filled in the gaps _too_ well; the extended paper is very long,
and the formalism it describes is incredibly complex. When we began this project
knowing only the abridged form of the system, we felt confident that we could
verify a sizable portion of it. After discovering the depth of the complete
specification, however, that goal seemed to get further from our grasp.

To amend this discrepancy, we simplified our target system as much as possible
while hopefully still retaining enough of the parts that make Curricle
interesting, with the eventual goal of adding complexity back (\ref{sec:chump}).
However, as of this writing, this reduced system remains unimplemented.


## Lattices

\begin{figure}
\begin{verbatim}
Class MeetSemiLattice (A : Type) :=
  { meet : A -> A -> A

  ; meet_commutative : forall x y,   meet x y          = meet y x
  ; meet_associative : forall x y z, meet (meet x y) z = meet x (meet y z)
  ; meet_idempotent  : forall x,     meet x x          = x }.

Class MeetOrder {A : Set} `(@MeetSemiLattice A) :=
  { pre             :  relation A
  ; preorder        :: PreOrder pre
  ; partial_order   :: PartialOrder eq pre
  ; meet_consistent :  forall x y, pre x y <-> x = (meet x y) }.
\end{verbatim}
\caption{Class definitions for semi-lattices.}
\label{lattice}
\end{figure}

Curricle's type system features a number of lattices; namely, the access
qualifiers, idempotence qualifiers, and taintedness qualifiers are all described
by the paper (whether in prose or by use of symbology such $\prec$, $\preceq$,
$\curlywedge$, $\sqsubset$, $\sqsubseteq$, $\sqcup$, etc) as being lattices
built from pre-order or partial order relations.

To that end, these authors sought to formalize these structures by way of a
generalized notion of lattices in Rocq. Our thinking was that, since so many
lattices are used (i.e., more than 2), and since the proofs of the interesting
parts of Curricle will need to explicitly refer to these relations, we would
develop a general theory for them. This would enable reuse of proof techniques
throughout our own proofs, but it would also reduce cognitive overhead.

Unfortunately, it seems that Rocq has managed to completely forego a standard
implementation of lattice proofs or classes, and, indeed, these authors were
unable to locate a correct implementation of such structures _at all_. We found
a paper describing a tactic to solve lattices [@LatticePaper], and what was
seemingly an implementation of this paper [@LatticeGitHub]. We spent a while
attempting to adapt this code to our needs. For example, the code implements
custom classes for partial orders (among other things), but such classes are
defined in the Rocq standard library, so we sought to adapt a new lattice
definition based on those found in this repository.

After much fiddling, we decided to develop our own (minimal) lattice
implementation from scratch, derived from what we had found. We decided to only
implement a semi-lattice (i.e., a lattice that only relates in one direction)
and reorient the Curricle structures to fit within this definition. Our
class definitions are shown in Figure \ref{lattice}. After this, we worked on
implementing instances of this class for the Curricle structures we needed.

Alas, for another obstacle then reared its head. Consider the definition of
"subtyping" for idempotence:

$$
\frac{qAcc \preceq_{a} qAcc'}{\text{Id}(qAcc) \sqsubseteq \text{Id}(qAcc')}
$$

\medskip

This seems simple enough: one idempotence qualifier is "less than or equal to"
another if the first's constituent access qualifier is "less than or equal to"
the second's. The access qualifiers are defined with the relations $\preceq_{a}$
and $\sim_{a}$:

$$
\text{Ck} \preceq_{a} \text{Wt} \sim_{a} (\text{Wt}^{t}\oplus\text{Rd})
\preceq_{a} (\text{Wt}\oplus\text{Rd})
$$
$$
\text{Ck} \preceq_{a} \text{Rd} \sim_{a} (\text{Wt}\oplus\text{Rd}^t) \sim_{a}
(\text{Wt}^{t}\oplus\text{Rd}^{t}) \preceq_{a} (\text{Wt}\oplus\text{Rd})
$$

\medskip

The operator $\preceq_{a}$ denotes a transitive and reflexive relation comparing
access qualifiers in the fashion typical of a partial order, and partial orders
are often one of the foundational pieces of a lattice definition. Meanwhile, the
operator $\sim_{a}$ represents a notion of "equivalence" among some of the
access qualifiers. These cannot all be fit into the same lattice, because they
violate some of the laws of how lattices operate --- namely, the presence of an
equivalence means that the lattice operations cannot be commutative, and the
partial order cannot be consistently reflexive.

To solve this problem, we have decided to simplify access qualifiers in our
mechanization. Our $\preceq_{a}$ relation is defined as:

$$
\text{Ck} \preceq_{a} \text{Wt}
$$
$$
\text{Ck} \preceq_{a} \text{Rd}
$$

\medskip

In other words, we have removed the $\oplus$-tagged qualifiers. This allows for
viewing the relation through the perspective of a semi-lattice, and it also
means we can move forward with the construction of proofs in terms of these
structures.


## Pointers

Our original specification for CHUMP included pointer values, along with
reference and dereference operators. We spent quite a bit of time mechanizing
this version of the project, including completion of proofs of progress and
preservation of the base type system. Unfortunately, as we moved from that point
to attempting to integrate additional Curricle systems, it became clear that
pointers and notions of ownership à la Rust really do make things hard when it
comes to mechanized verification.

To simplify our system (and hopefully render it tractable within the scope of a
class project), we eventually threw out pointers and reference/dereference
operations. We decided that if we can successfully prove the simpler system
correct, these would be among the first features we would add back in.


# Proof Set-Up

Similar to Curricle, we develop a theory of correctness derived from the notion
of \emph{non-interference}. We say that an intermittent execution of a program
is "correct" if there exists a continuous execution of the same program that,
given the same inputs, arrives at the same machine state. The word "same" is
doing a lot of work here, so we elaborate on what that means.

Intermittent execution is characterized by the presence of unpredictable power
failures followed by reboots. If we imagine a temperature-reading system
deployed in an environment with varying temperatures, it stands to reason that a
temporary shut-down would have a significant impact on the temperatures read by
the device relative to a similar nearby device that never experiences a
shut-down. If the program state is derived from inputs from the temperature
sensors, these devices would be likely to have noticeably different states at
the end of a given period of time.

However, in the realm of proof, we need not actually deploy devices. Instead, we
ask: "If a device with continuous execution were given the same inputs _as the
last successful regions of the intermittent computation_, would the outcomes be
the same?" To this end, we track the input and output as events in a log indexed
by the checkpoints and power failures. Thus, after an intermittent execution, we
can reconstitute a simulation of a continuous execution by discarding inputs and
outputs from repeated regions of code (i.e., code that ran but did not reach a
checkpoint prior to a power failure).

Unfortunately, we did not manage to specify our proofs in Rocq. This is due to
the system not being fully implemented (\ref{sec:challenges}, \ref{sec:eval}).
It seemed not worth the effort of writing down the proof statements if we did
not yet have the underlying system built, since the proof statements must be
written in terms of that system.


# Evaluation {#sec:eval}

When we began this work, we set evaluation goals we believed to be reasonable
[@PM2]. We now consider whether we have met these goals.


**A full specification of the syntax and semantics of CHUMP.** Although the
syntax has been solidified and much of the semantics defined, it is not
completely encoded in Rocq. We began this project by working on this and the
(revised) Curricle type system at the same time, but as the end of the semester
approached we focused more and more on the Curricle types rather than the base
system. We feel that this was the right choice, considering the implementation
of the Curricle system is the express purpose of the project, though it is
disappointing not to have completed this.

**Basic Curricle type system.** We have made significant headway relative to
where we began, including an implementation of the underlying type system
_beneath_ Curricle, but we have experienced setbacks at seemingly every possible
opportunity in the implementation of the more complex features
(\ref{sec:challenges}). The (re-)implementation of a complex system in a
theorem-proving language is not straightforward, as it turns out, and we
severely underestimated the effort it would take to accomplish our goals.

**Proofs of correctness started, if not proven.** Although we have produced
verified proofs of progress and preservation for the base type system, these
were not the proofs we had been particularly interested in writing. In fact, we
have not even formally specified the intended proof statements in Rocq, which
was a lesser form of this goal we had previously set. But this is not without
reason. Without the completed Rocq implementation of the Curricle system, it is
nearly impossible to actually phrase the proofs to any significant degree.
Anything we write is no better than a prose statement of intent, and we do not
see much point in spending effort on this while the base system remains
incomplete.

**Further goals.** In addition to our base goals, we had set a number of
additional goals we wanted to reach. Considering the state of everything else,
these authors feel it not worth expanding on the further aims that we also did
not satisfy.


# Future Work

The most pressing issue for this work is the successful implementation of the
basic Curricle type system. We believe that if this were to be completed
successfully and proofs of correctness satisfied, the additional features would
be significantly more straightforward to implement. In other words, CHUMP is
very front-loaded in terms of programmer effort, and while we do not believe the
rest of the project would necessarily be "easy", it seems reasonable to expect
it would be a much quicker process.


## Conclusion

Regretfully, we must admit defeat. The CHUMP system remains incomplete and our
desired proofs unproven. However, we feel that we have learned a lot through
this endeavor. Some brief takeaways:

  * Mechanized formal verification is hard.
  * Deep understanding of the entire system beforehand is necessary.
  * Papers often do not specify things in the way we might like.
  * Mechanized formal verification is hard.


# References
