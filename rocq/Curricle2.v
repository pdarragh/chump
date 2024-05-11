From ExtLib.Structures  Require Import Monad Traversable Foldable Reducible.
From ExtLib.Data        Require Import List Positive.
From ExtLib.Data.Monads Require Import OptionMonad.
From ExtLib.Data.Map    Require Import FMapPositive.

Import ListNotations.
Local Open Scope list_scope.

Import MonadNotation.
Local Open Scope monad_scope.

Definition var : Type := nat.
Definition loc : Type := positive.

Variant op1 := Not.
Variant op2 := Plus | Minus | Mult | And | Or | Eq.

Inductive val :=
| vInt  (i : Z)
| vBool (b : bool).

Inductive exp :=
| Int  (i : Z)
| Bool (b : bool)
| Op1  (o : op1) (e : exp)
| Op2  (o : op2) (e1 : exp) (e2 : exp).

Inductive cmd :=
| Noop
| Let        (e  : exp) (b  : cmd)
| LetInput   (b  : cmd)
| If         (e1 : exp) (e2 : exp) (e3 : exp)
| Output     (e  : exp)
| Seq        (c1 : cmd) (c2 : cmd)
| Checkpoint (ls : list loc).

(* An environment maps variables to locations, but variables are De Brujin
   indices mapped by list position. Consider the following program:

     let x = 42 in
     output x;
     let y = 17 in
     let z = x + y in
     output z

   We would expect [x] to have the index [0] at [output x], and the location
   corresponding to [x] would be the sole element in the environment list. By
   the time of [output z], if the environment maps [x] to [100], [y] to [200],
   and [z] to [300], we would expect the list to look like:

      [100; 200; 300]

   So [x], [y], and [z] would have indices [0], [1], and [2], respectively. *)
Definition env := list loc.

Record store := mkStore { st_next : positive
                        ; st_map  : pmap loc }.

Inductive kont :=
| kMt
| kSeq (c2 : cmd) (E : env) (k : kont).

Definition checkpoint : Type := kont * list (loc * val).

Definition CESKP : Type := cmd * env * store * kont * checkpoint.

Variant event :=
  | ePure       (M : CESKP)
  | eInput      (f : Z -> CESKP)
  | eOutput     (M : CESKP) (o : Z)
  | eCheckpoint (M : CESKP).

Variant io_event :=
  | io_in  (i : Z)
  | io_out (i : Z)
  | io_check
  | io_reset.

Definition io_log := list io_event.

Definition state : Type := CESKP * io_log.

Inductive ty := tInt | tBool.

(* Access qualifiers form a (very small) semilattice:

    Rd    Wt
      \  /
       Ck

   NOTE: If a Rd⊕Wt qualifier is added, I think it goes above both Rd and Wt. *)
Inductive access := Wt | Rd | Ck.

Reserved Notation "a1 'a≺' a2" (at level 40).
Reserved Notation "a1 'a≼' a2" (at level 40).
Reserved Notation "a1 'a⋏' a2 'a=' a3" (at level 40).

Inductive accessR : access -> access -> Prop :=
| accessWt : Ck a≺ Wt
| accessRd : Ck a≺ Rd
where "a1 'a≺' a2" := (accessR a1 a2).

Inductive accessRe : access -> access -> Prop :=
| accessStrict : forall a1 a2, a1 a≺ a2 -> a1 a≼ a2
| accessTrans : forall a1 a2 a3, a1 a≼ a2 -> a2 a≼ a3 -> a1 a≼ a3
| accessRefl : forall a, a a≼ a
where "a1 'a≼' a2" := (accessRe a1 a2).

Inductive accessMeet : access -> access -> access -> Prop :=
| accessMeetCk : forall a, Ck a⋏ a a= Ck
| accessMeetRdWt : Rd a⋏ Wt a= Ck
| accessMeetComm : forall a1 a2 a3, a1 a⋏ a2 a= a3 -> a2 a⋏ a1 a= a3
| accessMeetRefl : forall a, a a⋏ a a= a
where "a1 'a⋏' a2 'a=' a3" := (accessMeet a1 a2 a3).

(* Idempotence qualifiers form a (somehow smaller) semilattice:

     Id
      |
     Nid *)
Inductive idem := Nid | Id (macc : option access).

Reserved Notation "i1 'i≺' i2" (at level 40).
Reserved Notation "i1 'i≼' i2" (at level 40).
Reserved Notation "i1 'i⋏' i2 i= i3" (at level 40).

Inductive idemR : idem -> idem -> Prop :=
| idemId : forall q, Id q i≺ Nid
where "i1 'i≺' i2" := (idemR i1 i2).

Inductive idemRe : idem -> idem -> Prop :=
| idemAcc : forall a1 a2, a1 a≼ a2 -> Id (Some a1) i≼ Id (Some a2)
| idemStrict : forall i1 i2, i1 i≼ i2 -> i1 i≼ i2
| idemRefl : forall i, i i≼ i
where "i1 'i≼' i2" := (idemRe i1 i2).

Inductive idemMeet : idem -> idem -> idem -> Prop :=
| idemMeetIdSome : forall a1 a2 a3,
    a1 a⋏ a2 a= a3 ->
    Id (Some a1) i⋏ Id (Some a2) i= Id (Some a3)
| idemMeetIdNone : forall a, Id (Some a) i⋏ Id None i= Id (Some a)
| idemMeetNid : forall a, Id (Some a) i⋏ Nid i= Nid
| idemMeetComm : forall a1 a2 a3,
    a1 i⋏ a2 i= a3 ->
    a2 i⋏ a1 i= a3
| idemMeetRefl : forall a, a i⋏ a i= a
where "i1 'i⋏' i2 'i=' i3" := (idemMeet i1 i2 i3).

(* Taintedness is also a two-element semilattice:

     Nt
      |
     Tnt *)
Inductive taint := Nt | Tnt.

Reserved Notation "t1 't≺' t2" (at level 40).
Reserved Notation "t1 't≼' t2" (at level 40).
Reserved Notation "t1 't⋏' t2 't=' t3" (at level 40).

Inductive taintR : taint -> taint -> Prop :=
| taintNt : Nt t≺ Tnt
where "t1 't≺' t2" := (taintR t1 t2).

Inductive taintRe : taint -> taint -> Prop :=
| taintStrict : forall t1 t2, t1 t≺ t2 -> t1 t≼ t2
| taintRefl : forall t, t t≼ t
where "t1 't≼' t2" := (taintRe t1 t2).

Inductive taintMeet : taint -> taint -> taint -> Prop :=
| taintMeetTnt : forall t, Tnt t⋏ t t= Tnt
| taintMeetComm : forall t1 t2 t3,
    t1 t⋏ t2 t= t3 ->
    t2 t⋏ t1 t= t3
| taintMeetRefl : forall t, t t⋏ t t= t
where "t1 't⋏' t2 't=' t3" := (taintMeet t1 t2 t3).

Definition tyqual : Type := idem * taint.

Reserved Notation "tq1 '⊏' tq2" (at level 40).
Reserved Notation "tq1 '⊑' tq2" (at level 40).
Reserved Notation "tq1 '⊔' tq2 '==' tq3" (at level 40).

Inductive tyqualR : tyqual -> tyqual -> Prop :=
| tyQualSub' : forall (i1 i2 : idem) (t1 t2 : taint),
    i1 i≺ i2 ->
    t1 t≺ t2 ->
    (i1, t1) ⊏ (i2, t2)
where "tq1 '⊏' tq2" := (tyqualR tq1 tq2).

Inductive tyqualRe : tyqual -> tyqual -> Prop :=
| tyQualSubStrict : forall tq1 tq2, tq1 ⊏ tq2 -> tq1 ⊑ tq2
| tyQualSubRefl : forall tq, tq ⊑ tq
where "tq1 '⊑' tq2" := (tyqualRe tq1 tq2).

Inductive tyqualMeet : tyqual -> tyqual -> tyqual -> Prop :=
| tyQualMeet' : forall (i1 i2 i3 : idem) (t1 t2 t3 : taint),
    i1 i⋏ i2 i= i3 ->
    t1 t⋏ t2 t= t3 ->
    (i1, t1) ⊔ (i2, t2) == (i3, t3)
where "tq1 '⊔' tq2 '==' tq3" := (tyqualMeet tq1 tq2 tq3).
