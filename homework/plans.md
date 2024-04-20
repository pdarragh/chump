# Specification Language for Checkpointing


## Overview

  * an IMP-like language with checkpoints
  * language implemented in Roq
  * given a program with checkpoints, automatically deduce memory locations that
    can be saved via static analysis
      * future work: automatically deduce checkpoint insertion positions
  * develop a formal semantics for this language
  * use a CESK-like presentation with the property that steps can
    non-deterministically move to a power-off state, modeling intermittent
    computation
      * modified CESK includes both volatile and non-volatile stores
  * prove that running the checkpointed code in the system with power-offs
    produces the same end result as running on a system with continuous power


## Contributions

  1. New small language with checkpoint primitives.
  2. A formalization of checkpoint semantics, derived from the CESK style.
  3. A mechanization of the formal model of (2).
  4. A static analysis to identify sets of memory locations that need to be
     saved at checkpoints to maintain consistency with fully powered execution.
