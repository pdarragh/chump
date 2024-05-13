From Coq Require Import RelationClasses Relation_Definitions.

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

Class MeetSemiLattice (A : Type) :=
  { meet : A -> A -> A

  ; meet_commutative : forall x y,   meet x y          = meet y x
  ; meet_associative : forall x y z, meet (meet x y) z = meet x (meet y z)
  ; meet_idempotent  : forall x,     meet x x          = x
  }.

Class MeetOrder {A : Set} `(@MeetSemiLattice A) :=
  { pre             :  relation A
  ; preorder        :: PreOrder pre
  ; partial_order   :: PartialOrder eq pre
  ; meet_consistent :  forall x y, pre x y <-> x = (meet x y)
  }.

Inductive ty := tInt | tBool.

(* Access qualifiers form a (very small) semilattice:

    Rd    Wt
      \  /
       Ck

   NOTE: If a Rd⊕Wt qualifier is added, I think it goes above both Rd and Wt. *)
Inductive access := Wt | Rd | Ck.

Hint Constructors access : core.

Inductive accessR : access -> access -> Prop :=
| accessWt : accessR Ck Wt
| accessRd : accessR Ck Rd.

Hint Constructors accessR : core.

Instance accessR_Irreflexive : Irreflexive accessR.
Proof.
  unfold Irreflexive, Reflexive, complement.
  intros a H; inversion H.
Qed.

Instance accessR_Transitive : Transitive accessR.
Proof.
  unfold Transitive.
  intros a1 a2 a3 H1 H2; inversion H1; subst; inversion H2; subst.
Qed.

Instance accessR_StrictOrder : StrictOrder accessR :=
  { StrictOrder_Irreflexive := accessR_Irreflexive
  ; StrictOrder_Transitive  := accessR_Transitive }.

Inductive accessRe : access -> access -> Prop :=
| accessStrict : forall a1 a2,
    accessR a1 a2 ->
    accessRe a1 a2
| accessRefl : forall a,
    accessRe a a.

Hint Constructors accessRe : core.

Instance accessRe_Transitive : Transitive accessRe.
Proof.
  unfold Transitive.
  intros a1 a2 a3 H1 H2; inversion H1; subst; inversion H2; subst; auto.
  apply accessStrict; transitivity a2; assumption.
Qed.

Instance accessRe_PreOrder : PreOrder accessRe :=
  { PreOrder_Reflexive  := accessRefl
  ; PreOrder_Transitive := accessRe_Transitive }.

Instance accessRe_PartialOrder : PartialOrder (@eq access) accessRe.
Proof.
  unfold PartialOrder; cbn.
  intros a1 a2; split; intro H.
  * subst; split; reflexivity.
  * destruct H as [H1 H2].
    inversion H1; subst; inversion H2; subst; try reflexivity.
    inversion H; subst; inversion H0.
Qed.

Fixpoint accessMeet (a1 a2 : access) : access :=
  match a1, a2 with
  | Rd, Rd => Rd
  | Wt, Wt => Wt
  | _ , _  => Ck
  end.

Theorem accessMeet_Commutative : forall a1 a2, accessMeet a1 a2 = accessMeet a2 a1.
Proof. intros a1 a2; destruct a1, a2; reflexivity. Qed.

Theorem accessMeet_Associative : forall a1 a2 a3,
    accessMeet (accessMeet a1 a2) a3 = accessMeet a1 (accessMeet a2 a3).
Proof. intros a1 a2 a3; destruct a1, a2, a3; reflexivity. Qed.

Theorem accessMeet_Idempotent : forall a, accessMeet a a = a.
Proof. intro a; destruct a; reflexivity. Qed.

Instance access_MSL : MeetSemiLattice access :=
  { meet             := accessMeet
  ; meet_commutative := accessMeet_Commutative
  ; meet_associative := accessMeet_Associative
  ; meet_idempotent  := accessMeet_Idempotent }.

Theorem accessMeet_Consistent : forall a1 a2, accessRe a1 a2 <-> a1 = (accessMeet a1 a2).
Proof.
  intros a1 a2; split.
  * intro Hacc; inversion Hacc; subst.
    - inversion H; subst.
      + reflexivity.
      + reflexivity.
    - destruct a2; reflexivity.
  * intro Heq.
    rewrite Heq.
    destruct a1, a2; auto.
Qed.

Instance access_MO : MeetOrder access_MSL :=
  { pre             := accessRe
  ; preorder        := accessRe_PreOrder
  ; partial_order   := accessRe_PartialOrder
  ; meet_consistent := accessMeet_Consistent }.

(* Idempotence qualifiers form a (somehow smaller) semilattice:

     Nid
      |
     Id *)
Inductive idem := Nid | Id | IdAcc (a : access).

Hint Constructors idem : core.

Inductive idemR : idem -> idem -> Prop :=
| idemNidId      :                          idemR  Nid        Id
| idemNidIdAcc   : forall a,                     idemR  Nid       (IdAcc a)
| idemIdAccId    : forall a,                     idemR (IdAcc a)   Id
| idemIdAccIdAcc : forall a1 a2, accessR a1 a2 -> idemR (IdAcc a1) (IdAcc a2).

Hint Constructors idemR : core.

Instance idemR_Irreflexive : Irreflexive idemR.
Proof.
  unfold Irreflexive, Reflexive, complement.
  intros i H1; inversion H1; subst; inversion H2; subst.
Qed.

Instance idemR_Transitive : Transitive idemR.
Proof.
  unfold Transitive.
  intros i1 i2 i3 H1 H2; inversion H1; subst; inversion H2; subst; auto.
  inversion H; subst; inversion H3; subst.
Qed.

Instance idemR_StrictOrder : StrictOrder idemR :=
  { StrictOrder_Irreflexive := idemR_Irreflexive
  ; StrictOrder_Transitive  := idemR_Transitive }.

Inductive idemRe : idem -> idem -> Prop :=
| idemStrict : forall i1 i2,
    idemR  i1 i2 ->
    idemRe i1 i2
| idemRefl : forall i,
    idemRe i i.

Hint Constructors idemRe : core.

Instance idemRe_Transitive : Transitive idemRe.
Proof.
  unfold Transitive.
  intros i1 i2 i3 H1 H2; inversion H1; subst; inversion H2; subst; auto.
  apply idemStrict; transitivity i2; assumption.
Qed.

Instance idemRe_PreOrder : PreOrder idemRe :=
  { PreOrder_Reflexive  := idemRefl
  ; PreOrder_Transitive := idemRe_Transitive }.

Instance idemRe_PartialOrder : PartialOrder (@eq idem) idemRe.
Proof.
  unfold PartialOrder; cbn.
  intros i1 i2; split; intro H; subst.
  * split; reflexivity.
  * destruct H as [H1 H2].
    inversion H1; subst; inversion H2; subst; auto.
    inversion H; subst; inversion H0; subst.
    inversion H3; subst; inversion H6; subst.
Qed.

Fixpoint idemMeet (i1 i2 : idem) : idem :=
  match i1, i2 with
  | IdAcc a1, IdAcc a2 => IdAcc (accessMeet a1 a2)
  | IdAcc a , Id       => IdAcc a
  | Id      , IdAcc a  => IdAcc a
  | Id      , Id       => Id
  | _       , _        => Nid
  end.

Theorem idemMeet_Commutative : forall i1 i2, idemMeet i1 i2 = idemMeet i2 i1.
Proof.
  intros i1 i2; destruct i1 as [| | a1], i2 as [| | a2]; try reflexivity.
  destruct a1, a2; reflexivity.
Qed.

Theorem idemMeet_Associative : forall i1 i2 i3,
    idemMeet (idemMeet i1 i2) i3 = idemMeet i1 (idemMeet i2 i3).
Proof.
  intros i1 i2 i3; destruct i1 as [| | a1], i2 as [| | a2], i3 as [| | a3]; try reflexivity.
  destruct a1, a2, a3; reflexivity.
Qed.

Theorem idemMeet_Idempotent : forall i, idemMeet i i = i.
Proof.
  intro i; destruct i; try reflexivity.
  destruct a; reflexivity.
Qed.

Instance idem_MSL : MeetSemiLattice idem :=
  { meet             := idemMeet
  ; meet_commutative := idemMeet_Commutative
  ; meet_associative := idemMeet_Associative
  ; meet_idempotent  := idemMeet_Idempotent }.

Theorem idemMeet_Consistent : forall i1 i2, idemRe i1 i2 <-> i1 = (idemMeet i1 i2).
Proof.
  intros i1 i2; split.
  * intro Hidem; inversion Hidem; subst.
    - inversion H; subst; auto.
      inversion H0; subst; auto.
    - destruct i2; auto.
      destruct a; auto.
  * intro Heq.
    rewrite Heq.
    destruct i1 as [| | a1], i2 as [| | a2]; auto.
    - destruct a1; cbn; auto.
    - destruct a1, a2; cbn; auto.
Qed.

Instance idem_MO : MeetOrder idem_MSL :=
  { pre             := idemRe
  ; preorder        := idemRe_PreOrder
  ; partial_order   := idemRe_PartialOrder
  ; meet_consistent := idemMeet_Consistent }.

(* Taintedness is also a two-element semilattice:

     Tnt
      |
     Nt *)
Inductive taint := Nt | Tnt.

Hint Constructors taint : core.

Inductive taintR : taint -> taint -> Prop :=
| taintNt : taintR Tnt Nt.

Hint Constructors taintR : core.

Instance taintR_Irreflexive : Irreflexive taintR.
Proof.
  unfold Irreflexive, Reflexive, complement.
  intros t H; inversion H.
Qed.

Instance taintR_Transitive : Transitive taintR.
Proof.
  unfold Transitive.
  intros t1 t2 t3 H1 H2; inversion H1; subst; inversion H2; subst.
Qed.

Instance taintR_StrictOrder : StrictOrder taintR :=
  { StrictOrder_Irreflexive := taintR_Irreflexive
  ; StrictOrder_Transitive  := taintR_Transitive }.

Inductive taintRe : taint -> taint -> Prop :=
| taintStrict : forall t1 t2,
    taintR  t1 t2 ->
    taintRe t1 t2
| taintRefl : forall t,
    taintRe t t.

Hint Constructors taintRe : core.

Instance taintRe_Transitive : Transitive taintRe.
Proof.
  unfold Transitive.
  intros t1 t2 t3 H1 H2; inversion H1; subst; inversion H2; subst; auto.
  apply taintStrict; transitivity t2; assumption.
Qed.

Instance taintRe_PreOrder : PreOrder taintRe :=
  { PreOrder_Reflexive  := taintRefl
  ; PreOrder_Transitive := taintRe_Transitive }.

Instance taintRe_PartialOrder : PartialOrder (@eq taint) taintRe.
Proof.
  unfold PartialOrder; cbn.
  intros t1 t2; split; intro H.
  * subst; split; reflexivity.
  * destruct H as [H1 H2].
    inversion H1; subst; inversion H2; subst; auto.
    inversion H; subst; inversion H0.
Qed.

Fixpoint taintMeet (t1 t2 : taint) : taint :=
  match t1, t2 with
  | Nt, Nt => Nt
  | _ , _  => Tnt
  end.

Theorem taintMeet_Commutative : forall t1 t2, taintMeet t1 t2 = taintMeet t2 t1.
Proof. intros t1 t2; destruct t1, t2; reflexivity. Qed.

Theorem taintMeet_Associative : forall t1 t2 t3,
    taintMeet (taintMeet t1 t2) t3 = taintMeet t1 (taintMeet t2 t3).
Proof. intros t1 t2 t3; destruct t1, t2, t3; reflexivity. Qed.

Theorem taintMeet_Idempotent : forall t, taintMeet t t = t.
Proof. intro t; destruct t; reflexivity. Qed.

Instance taint_MSL : MeetSemiLattice taint :=
  { meet             := taintMeet
  ; meet_commutative := taintMeet_Commutative
  ; meet_associative := taintMeet_Associative
  ; meet_idempotent  := taintMeet_Idempotent }.

Theorem taintMeet_Consistent : forall t1 t2, taintRe t1 t2 <-> t1 = (taintMeet t1 t2).
Proof.
  intros t1 t2; split.
  * intro Htnt; inversion Htnt; subst.
    - inversion H; subst.
      reflexivity.
    - destruct t2; reflexivity.
  * intro Heq.
    rewrite Heq.
    destruct t1, t2; auto.
Qed.

Instance taint_MO : MeetOrder taint_MSL :=
  { pre             := taintRe
  ; preorder        := taintRe_PreOrder
  ; partial_order   := taintRe_PartialOrder
  ; meet_consistent := taintMeet_Consistent }.

Definition tyqual : Type := idem * taint.

Inductive tyqualR : tyqual -> tyqual -> Prop :=
| tyqualSub : forall (i1 i2 : idem) (t1 t2 : taint),
    idemR i1 i2 ->
    taintR t1 t2 ->
    tyqualR (i1, t1) (i2, t2).

Hint Constructors tyqualR : core.

Instance tyqualR_Irreflexive : Irreflexive tyqualR.
Proof.
  unfold Irreflexive, Reflexive, complement.
  intros tq1 Htyqual; inversion Htyqual as [i1 i2 t1 t2 Hidem Htaint]; inversion Htaint.
Qed.

Instance tyqualR_Transitive : Transitive tyqualR.
Proof.
  unfold Transitive.
  intros tq1 tq2 tq3 Htyqual12 Htyqual23.
  inversion Htyqual12 as [i1 i2 t1 t2 Hidem1 Htaint1]; subst.
  inversion Htyqual23 as [[] i3 [] t3 Hidem3 Htaint3]; subst;
    inversion Htaint1; inversion Htaint3.
Qed.

Instance tyqualR_StrictOrder : StrictOrder tyqualR :=
  { StrictOrder_Irreflexive := tyqualR_Irreflexive
  ; StrictOrder_Transitive  := tyqualR_Transitive }.

Inductive tyqualRe : tyqual -> tyqual -> Prop :=
| tyqualStrict : forall tq1 tq2,
    tyqualR  tq1 tq2 ->
    tyqualRe tq1 tq2
| tyqualIdemEquiv : forall (i1 i2 : idem) (t1 t2 : taint),
    idemRe i1 i2 /\ idemRe i2 i1 ->
    taintR t1 t2 ->
    tyqualRe (i1, t1) (i2, t2)
| tyqualTaintEquiv : forall (i1 i2 : idem) (t1 t2 : taint),
    idemR i1 i2 ->
    taintRe t1 t2 /\ taintRe t2 t1 ->
    tyqualRe (i1, t1) (i2, t2)
| tyqualRefl : forall tq,
    tyqualRe tq tq.


(* | tyqualStrict : forall q1 q2, *)
(*     tyqualR  q1 q2 -> *)
(*     tyqualRe q1 q2 *)
(* | tyqualRefl : forall q, *)
(*     tyqualRe q q. *)

Hint Constructors tyqualRe : core.

Instance tyqualRe_Transitive : Transitive tyqualRe.
Proof.
  unfold Transitive.
  intros tq1 tq2 tq3 H1 H2; inversion H1; subst; inversion H2; subst; auto.
  * inversion H; subst; inversion H0; subst.
    inversion H4; subst; inversion H9; subst.
  * inversion H3; subst.

(* Instance tyqualRe_Transitive : Transitive tyqualRe. *)
(* Proof. *)
(*   unfold Transitive. *)
(*   intros tq1 tq2 tq3 H1 H2; inversion H1; subst; inversion H2; subst; auto. *)
(*   apply tyqualStrict; transitivity tq2; assumption. *)
(* Qed. *)

(* Instance tyqualRe_PreOrder : PreOrder tyqualRe := *)
(*   { PreOrder_Reflexive  := tyqualRefl *)
(*   ; PreOrder_Transitive := tyqualRe_Transitive }. *)

(* Instance tyqualRe_PartialOrder : PartialOrder (@eq tyqual) tyqualRe. *)
(* Proof. *)
(*   unfold PartialOrder; cbn. *)
(*   intros tq1 tq2; split; intro H; subst. *)
(*   * split; reflexivity. *)
(*   * destruct H as [H1 H2]. *)
(*     inversion H1; subst; inversion H2; subst; auto. *)
(*     inversion H; subst; inversion H0; subst. *)
(*     inversion H4; subst; inversion H10; subst. *)
(* Qed. *)

Fixpoint tyqualMeet (tq1 tq2 : tyqual) : tyqual :=
  match tq1, tq2 with
  | (i1, t1), (i2, t2) =>
      let i3 := idemMeet  i1 i2 in
      let t3 := taintMeet t1 t2 in
      (i3, t3)
  end.

Theorem tyqualMeet_Commutative : forall tq1 tq2, tyqualMeet tq1 tq2 = tyqualMeet tq2 tq1.
Proof.
  intros tq1 tq2; destruct tq1 as [i1 t1], tq2 as [i2 t2].
  destruct i1 as [| | a1], i2 as [| | a2], t1, t2; auto; destruct a1, a2; auto.
Qed.

Theorem tyqualMeet_Associative : forall tq1 tq2 tq3,
    tyqualMeet (tyqualMeet tq1 tq2) tq3 = tyqualMeet tq1 (tyqualMeet tq2 tq3).
Proof.
  intros tq1 tq2 tq3; destruct tq1 as [i1 t1], tq2 as [i2 t2], tq3 as [i3 t3].
  destruct i1 as [| | a1], i2 as [| | a2], i3 as [| | a3], t1, t2, t3; auto; destruct a1, a2, a3; auto.
Qed.

Theorem tyqualMeet_Idempotent : forall tq, tyqualMeet tq tq = tq.
Proof.
  intro tq; destruct tq, i as [| | a], t; try reflexivity; destruct a; reflexivity.
Qed.

Instance tyqual_MSL : MeetSemiLattice tyqual :=
  { meet             := tyqualMeet
  ; meet_commutative := tyqualMeet_Commutative
  ; meet_associative := tyqualMeet_Associative
  ; meet_idempotent  := tyqualMeet_Idempotent }.

Theorem tyqualMeet_Consistent : forall tq1 tq2, tyqualRe tq1 tq2 <-> tq1 = (tyqualMeet tq1 tq2).
Proof.
  intros tq1 tq2; split.
  * intro Htyqual; inversion Htyqual; subst.
    - inversion H; subst; inversion H0; subst; inversion H1; subst; try reflexivity; inversion H2; subst; reflexivity.
    - destruct tq2 as [i2 t2], i2, t2; try reflexivity; destruct a; reflexivity.
  * intro Heq.
    rewrite Heq.
    destruct tq1 as [i1 t1], tq2 as [i2 t2]; try reflexivity.
    destruct i1 as [| | a1], i2 as [| | a2], t1, t2; try reflexivity.
    - cbn.
      apply tyqualStrict, tyqualSub.
      +
    ; destruct a1, a2; reflexivity.
