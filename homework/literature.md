# Literature Review

This file is just to organize thoughts about the papers that are related to our
project.

  * IMP reference
      * "Experience with an Extensible Language"
          * https://doi.org/10.1145%2F361953.361966
      * "Syntax Extension and the IMP72 Programming Language"
          * https://doi.org/10.1145%2F987413.987416
  * Undo checkpointing
      * Undo/redo log notes from Emory
          * http://www.cs.emory.edu/~cheung/Courses/554/Syllabus/6-logging/undo-redo3a.html
      * Chinchilla
          * https://www.usenix.org/system/files/osdi18-maeng.pdf
          * checkpoints good
          * existing automatic checkpoint systems over-checkpoint
          * this incurs performance penalties
          * manual checkpointing reduces "programmability"
          * "Avoiding non-termination is an important correctness property in an
            intermittent system that no prior system satisfactorily provides."
          * "Chinchilla does not ask the programmer to specify task boundaries"
      * "A survey and experimental analysis of checkpointing techniques for
        energy harvesting devices"
          * https://doi.org/10.1016/j.sysarc.2022.102464
  * Semantics of intermittent computation
      * "Towards a Formal Foundation of Intermittent Computing"
          * https://doi.org/10.1145/3428231
          * provides formal model of intermittent execution
          * makes reasonable assumptions
              * forward progress, i.e., no guarantee that energy will eventually
                be harvested that ensures the process completes
              * timeliness, i.e., no guarantee about total time taken, nor any
                guarantee about available data being still relevant when read
              * no concurrency
          * provides some related work to look through
          * defines what it means for an intermittent execution to be "correct"
      * "A Type System for Safe Intermittent Computing"
          * https://doi.org/10.1145/3591250
          * type-level reasoning about intermittent computing for Rust
          * rejects programs "causing undesired non-idempotence"
          * programmers manually annotate idempotence requirements
          * Curricle infers which variables must be recovered to satisfy the
            programmer's requirements via "information flow typing" and "type
            qualifiers denoting _access modes_"
      * "Using Crash Hoare Logic for Certifying the FSCQ File System"
          * https://people.csail.mit.edu/nickolai/papers/chen-fscq.pdf
          * not what we want
              * Justin talked to Miljana about it a bit and there was some
                specific issue that made it very difficult
              * kind of referenced in "Towards [...]"; maybe that's all?
  * Some CESK reference
  * Mechanizations of formal models in this space
