From Coq Require Import Relations RelationClasses List String ZArith FSets.FMapPositive Lia Setoid.

Import ListNotations.
Local Open Scope list_scope.

From ExtLib.Structures  Require Import Monad Traversable Foldable Reducible.
From ExtLib.Data        Require Import List.
From ExtLib.Data.Monads Require Import OptionMonad.

Import MonadNotation.
Open Scope monad_scope.

Set Implicit Arguments.
Generalizable All Variables.

Definition var : Type := nat.

Inductive pexp :=
| Var   (x : var)
| Deref (l : pexp).

Variant op1 := Not.
Variant op2 := Plus | Minus | Mult | And | Or | Eq.

Inductive exp :=
| Int  (i : Z)
| Bool (b : bool)
| Ref  (l : pexp)
| Load (l : pexp)
| Op1  (o : op1) (e : exp)
| Op2  (o : op2) (e1 : exp) (e2 : exp).

Inductive c :=
| Noop
| Let        (e    : exp)  (body : c)
| LetInput   (body : c)
| Assign     (l    : pexp) (e : exp)
| If         (e    : exp)  (thn: c) (els : c)
| Loop       (body : c)
| Break      (n    : nat)
| Output     (e    : exp)
| Seq        (s1   : c)    (s2 : c)
| Checkpoint (ls   : list pexp).

Definition addr := positive.
Definition env := list.
Definition lookup_env := nth_error.

Inductive val :=
| vInt  (i : Z)
| vBool (b : bool)
| vPtr  (p : addr).

Record store A := mkStore { st_next : positive ; st_map : PositiveMap.t A }.

Inductive kont :=
| kMt
| kSeq  (s2   : c) (E : env addr) (k : kont)
| kLoop (body : c) (E : env addr) (k : kont).

Definition checkpoint : Type := kont * list (addr * val).

Definition CESKP : Type := c * env addr * store val * kont * checkpoint.

Variant event :=
| ePure                        (st : CESKP)
| eInput      (f  : Z -> CESKP)
| eOutput     (o  : Z)         (st : CESKP)
| eCheckpoint                  (st : CESKP).

Variant io_event :=
| io_in  (i : Z)
| io_out (i : Z)
| io_check
| io_reset.

Definition io_log := list io_event.

Definition state : Type := CESKP * io_log.

Inductive ty := tInt | tBool | tPtr (t : ty).

(* Type Qualifier Lattice *)
Inductive qAcc :=
| Wt | Rd | Ck
| Wt_or_Rd
| WtT_or_Rd
| Wt_or_RdT
| WtT_or_RdT.

Reserved Notation "q1 '~=' q2" (at level 40).

Variant qAccEquiv : qAcc -> qAcc -> Prop :=
  | qAccEquivWt : Wt ~= WtT_or_Rd
  | qAccEquivWtT_or_Rd : WtT_or_Rd ~= Wt
  | qAccEquivRd1 : Rd ~= Wt_or_RdT
  | qAccEquivRd2 : Rd ~= WtT_or_RdT
  | qAccEquivWt_or_RdT1 : Wt_or_RdT ~= Rd
  | qAccEquivWt_or_RdT2 : Wt_or_RdT ~= WtT_or_RdT
  | qAccEquivWtT_or_RdT1 : WtT_or_RdT ~= Rd
  | qAccEquivWtT_or_RdT2 : WtT_or_RdT ~= Wt_or_RdT
  | qAccEquivRefl : forall q, q ~= q
where "q1 '~=' q2" := (qAccEquiv q1 q2).

Instance qAccEquivRefl_ : Reflexive qAccEquiv := { reflexivity := qAccEquivRefl }.

Lemma qAccEquivTrans : Transitive qAccEquiv.
Proof.
  unfold Transitive.
  intros q1 q2 q3 H0 H1.
  inversion H0; inversion H1; try apply qAccEquivSelf; try congruence; try econstructor.
Qed.

Lemma qAccEquivSym : Symmetric qAccEquiv.
Proof. unfold Symmetric. intros; inversion H; constructor. Qed.

Instance qAccEquivEquiv : Equivalence qAccEquiv :=
  {
    Equivalence_Reflexive := qAccEquivRefl;
    Equivalence_Symmetric := qAccEquivSym;
    Equivalence_Transitive := qAccEquivTrans
  }.

Reserved Notation "q1 'pre<=' q2" (at level 40).

Inductive qAccR : qAcc -> qAcc -> Prop :=
| qAccWt : Ck pre<= Wt
| qAccWtT_or_Rd : Ck pre<= WtT_or_Rd
| qAccWt_or_Rd1 : Wt pre<= Wt_or_Rd
| qAccWt_or_Rd2 : WtT_or_Rd pre<= Wt_or_Rd
| qAccRd : Ck pre<= Rd
| qAccWt_or_RdT : Rd pre<= Wt_or_RdT
| qAccWtT_or_RdT : Rd pre<= WtT_or_RdT
| qAccWt_or_Rd3 : Rd pre<= Wt_or_Rd
| qAccWt_or_Rd4 : Wt_or_RdT pre<= Wt_or_Rd
| qAccWt_or_Rd5 : WtT_or_RdT pre<= Wt_or_Rd
| qAccTrans : forall q1 q2 q3, q1 pre<= q2 -> q2 pre<= q3 -> q1 pre<= q3
| qAccSub : forall q1 q2 q3, q1 ~= q2 -> q1 pre<= q3 -> q2 pre<= q3
| qAccRefl : forall q, q pre<= q
where "q1 'pre<=' q2" := (qAccR q1 q2).

Instance qAccRTrans : Transitive qAccR := { transitivity := qAccTrans }.
Instance qAccRRefl  : Reflexive  qAccR := { reflexivity  := qAccRefl }.

Instance qAccPO : PreOrder qAccR :=
  {
    PreOrder_Reflexive := qAccRRefl;
    PreOrder_Transitive := qAccRTrans
  }.

Reserved Infix "sqcup" (at level 40, left associativity).

(* Class UpLattice (A : Set) := *)
(*   { *)
(*     lattice_le : A -> A -> Prop; *)

(*     join : A -> A -> A where "x 'sqcup' y" := (join x y); *)

(*     join_commutative : forall a b,         a sqcup b = b sqcup a; *)
(*     join_associative : forall a b c, (a sqcup b) sqcup c = a sqcup (b sqcup c); *)
(*     join_idempotent  : forall a,           a sqcup a = a *)
(*   }. *)

Class UpLattice {A : Type} (R : relation A) : Prop :=
  {
    join : A -> A -> A where "x 'sqcup' y" := (join x y);

    join_commutative : forall a b,         a sqcup b = b sqcup a;
    join_associative : forall a b c, (a sqcup b) sqcup c = a sqcup (b sqcup c);
    join_idempotent  : forall a,           a sqcup a = a
  }.

Infix "sqcup" := join (at level 40, left associativity).

Inductive qAccJoin : qAcc -> qAcc -> qAcc -> Prop :=
| qAccJoinComm : forall q1 q2 q3, qAccJoin q1 q2 q3 -> qAccJoin q2 q1 q3
| qAccJoinSelf : forall q, qAccJoin q q q
| qAccJoinPre : forall q1 q2, q1 pre<= q2 -> qAccJoin q1 q2 q2
| qAccJoinAssoc : forall q1 q2 q3 q4 q5 q6,
    qAccJoin q1 q2 q4 ->         (* q1 R q2 = q4 *)
    qAccJoin q4 q3 q5 ->         (* q4 R q3 = q5 *)
    qAccJoin q2 q3 q6 ->         (* q2 R q3 = q6 *)
    qAccJoin q1 q6 q5.          (* q1 R q6 = q5 *)

(* Instance qAccJoinUp : UpLattice qAccR := *)
(*   { *)
(*     join := qAccJoin *)
(*   }. *)

(* Definition qAccJoin (q1 q2 : qAcc) : option qAcc := *)
(*   match q1, q2 with *)
(*   | Ck, _ => q2 *)
(*   | _, Ck => q1 *)
(*   | Wt_or_Rd, _ => q1 *)
(*   | _, Wt_or_Rd => q2 *)

(*   end. *)



(* Inductive qAccJoin : qAcc -> qAcc -> Prop := *)
(* | qAccJoinConsistent : forall q1 q2, qAccJoin q1 q2 <-> q2 ~= (qAccJoin q1 q2). *)

(* | qAccJoinCk : forall q, qAccJoin Ck q = Ck. *)
(* | qAccJoinComm : forall q1 q2 q3, qAccJoin q1 q2 q3 -> qAccJoin q2 q1 q3 *)

(* Definition qAccJoin (q1 q2 : qAcc) : qAcc := *)
(*   match q1, q2 with *)

(*   end. *)
(* Defined. *)


(* Instance qAccUL : UpLattice qAccR := *)
(*   { *)
(*     join := qAccR; *)
(*     join_commutative :=  *)
(*   } *)

(* Definition join_consistent := forall a b, a sqcup b <-> b = a sqcup b. *)

(* Class UpSet {A : Set} `(@PreOrder A) `(@UpLattice A) := *)
(*   { *)
(*     join_consistent := forall a b, A.R a b <-> b = a sqcup b *)
(*   }. *)

(* Context `{L : UpLattice A}. *)

(* Theorem join_is_lub : forall a b : A, *)
(*   forall x, (lattice_le a x) /\ (lattice_le b x) <-> (lattice_le (a sqcup b) x). *)
(* Proof. *)
(*   split; intros. *)
(*   * intuition. *)



(*   Class Lattice (A : Type) := { *)
(*   meet : A -> A -> A where "x ⊓ y" := (meet x y); *)
(*   join : A -> A -> A where "x ⊔ y" := (join x y); *)

(*   meet_commutative : forall a b, a ⊓ b = b ⊓ a; *)
(*   meet_associative : forall a b c, (a ⊓ b) ⊓ c = a ⊓ (b ⊓ c); *)
(*   meet_absorptive  : forall a b, a ⊓ (a ⊔ b) = a; *)
(*   meet_idempotent  : forall a, a ⊓ a = a; *)

(*   join_commutative : forall a b, a ⊔ b = b ⊔ a; *)
(*   join_associative : forall a b c, (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c); *)
(*   join_absorptive  : forall a b, a ⊔ (a ⊓ b) = a; *)
(*   join_idempotent  : forall a, a ⊔ a = a *)
(* }. *)








(* Idemptotent Qualifier Lattice *)
Inductive idem := Nid | Id (mq : option qAcc).

Inductive idemR : idem -> idem -> Prop :=
| idemId : forall q, idemR (Id q) Nid.

Inductive idemRe : idem -> idem -> Prop :=
| idemAcc    : forall q1 q2, q1 pre<= q2     -> idemRe (Id (Some q1)) (Id (Some q2))
| idemStrict : forall i1 i2, idemR i1 i2 -> idemRe i1             i2
| idemRefl   : forall i,                   idemRe i              i.

Instance idemReRefl : Reflexive idemRe := { reflexivity := idemRefl }.

Inductive idemJoin : idem -> idem -> idem -> Prop :=
| idemJoinIdSome : forall q1 q2 q3, qAccJoin q1 q2 q3 -> idemJoin (Id (Some q1)) (Id (Some q2)) (Id (Some q3))
| idemJoinIdNone : forall q, idemJoin (Id (Some q)) (Id None) (Id (Some q))
| idemJoinNid : forall q, idemJoin (Id (Some q)) Nid Nid
| idemJoinComm : forall q1 q2 q3, idemJoin q1 q2 q3 -> idemJoin q2 q1 q3
| idemJoinSelf : forall q, idemJoin q q q.

Inductive idemExtractqAcc : idem -> option qAcc -> Prop :=
| idemExtractId : forall q, idemExtractqAcc (Id q) q
| idemExtractNid : idemExtractqAcc Nid None.

Inductive qAccROpt : option qAcc -> qAcc -> Prop :=
| qAccSome : forall q, qAccROpt (Some q) q
| qAccNone : qAccROpt None Ck.

(* Inductive idemJoinqAcc : idem -> qAcc -> qAcc -> Prop := *)
(* | idemJoinqAccIdSome : forall q1 q2 q3, qAccJoin q1 q2 q3 -> idemJoinqAcc (Id (Some q1)) q2 q3 *)
(* | idemJoinqAccIdNone : forall q, idemJoinqAcc (Id None) q q. *)

Inductive taint := Nt | Tnt.

Inductive taintR : taint -> taint -> Prop := taintNt : taintR Nt Tnt.

Inductive taintRe : taint -> taint -> Prop :=
| taintStrict : forall t1 t2, taintR t1 t2 -> taintRe t1 t2
| taintRefl : forall t, taintRe t t.

Instance taintReRefl : Reflexive taintRe := { reflexivity := taintRefl }.

Inductive taintJoin : taint -> taint -> taint -> Prop :=
| taintJoinTnt : forall t, taintJoin t Tnt Tnt.

Definition tyQual : Type := idem * taint.

Reserved Notation "tq1 'sqsub' tq2" (at level 40).

Inductive tyQualSub : tyQual -> tyQual -> Prop :=
| tyQualSubParts : forall (i1 i2 : idem) (t1 t2: taint), idemR i1 i2 -> taintR t1 t2 -> (i1, t1) sqsub (i2, t2)
where "tq1 'sqsub' tq2" := (tyQualSub tq1 tq2).

Reserved Notation "tq1 'sqsub=' tq2" (at level 40).

Inductive tyQualSubE : tyQual -> tyQual -> Prop :=
| tyQualSubStrict : forall tq1 tq2, tq1 sqsub tq2 -> tq1 sqsub= tq2
| tyQualSubRefl : forall tq, tq sqsub= tq
where "tq1 'sqsub=' tq2" := (tyQualSubE tq1 tq2).

Instance tyQualSubERefl : Reflexive tyQualSubE := { reflexivity := tyQualSubRefl }.

Inductive tyQualJoin : tyQual -> tyQual -> tyQual -> Prop :=
| tyQualJoin' : forall (i1 i2 i3 : idem) (t1 t2 t3 : taint),
    idemJoin i1 i2 i3 ->
    taintJoin t1 t2 t3 ->
    tyQualJoin (i1, t1) (i2, t2) (i3, t3).




Inductive has_tyQual_pexp : env tyQual -> pexp -> tyQual -> Prop :=
| has_tyQual_Var : forall G x tq,
    lookup_env G x = Some tq ->
    has_tyQual_pexp G (Var x) tq
| has_ty_Deref : forall G p tq,
    has_tyQual_pexp G p tq ->
    has_tyQual_pexp G (Deref p) tq. (* TODO: Correct? *)

Inductive has_tyQual_exp : env tyQual -> exp -> tyQual -> Prop :=
(* Literals are automatically unquestionably idempotent and untainted. *)
| has_tyQual_Int  : forall G i, has_tyQual_exp G (Int i)  (Id None, Nt)
| has_tyQual_Bool : forall G b, has_tyQual_exp G (Bool b) (Id None, Nt)

(* References are TODO. *)
| has_tyQual_Ref  : forall G p tq,
    has_tyQual_pexp G p tq ->
    has_tyQual_exp G (Ref p) tq (* some kind of Read here *)

| has_tyQual_Load : forall G p tq,
    has_tyQual_pexp G p tq ->
    has_tyQual_exp G (Load p) tq (* ??? *)

(* Unary and binary operations are unable to affect type qualifiers. *)
| has_tyQual_Op1  : forall G o e tq,
    has_tyQual_exp G e tq ->
    has_tyQual_exp G (Op1 o e) tq
| has_tyQual_Op2  : forall G o e1 e2 tq1 tq2 tq3,
    has_tyQual_exp G e1 tq1 ->
    has_tyQual_exp G e2 tq2 ->
    tyQualJoin tq1 tq2 tq3 ->
    has_tyQual_exp G (Op2 o e1 e2) tq3.

(* Command type qualifier checking updates the environment and list of *)
(* written-to locations. *)
(* Inductive has_tyQual_c : env tyQual -> list pexp -> c -> env tyQual -> list pexp -> Prop := *)
(* | has_tyQual_Noop : forall G wts, has_tyQual_c G wts Noop G wts *)
(* | has_tyQual_Let : forall G wts e tq c, *)
(*     has_tyQual_exp G e tq -> *)
(*     has_tyQual_c (tq :: G) c -> *)
(*     has_tyQual_c G (Let e c). *)


(* "The command checking judgments can update the point to and write sets. It *)
(*  may also update the taints in types." *)

Inductive has_tyQual_c : tyQual -> env tyQual -> list pexp -> c -> Prop :=
| has_tyQual_Noop : forall tq0 G wts, has_tyQual_c tq0 G wts Noop

| has_tyQual_Let : forall tq0 G wts e tq1 tq2 c,
    has_tyQual_exp G e tq1 ->
    tyQualJoin tq0 tq1 tq2 ->
    has_tyQual_c tq0 (tq2::G) wts c -> (* TODO: update [wts] *)
    has_tyQual_c tq0 G wts (Let e c)

    (* Original version below. I'm not sure why it doesn't work this way. *)
    (* qAccJoin qAcc Wt qAcc' -> *)
    (* has_tyQual_c ((qAcc', qId) :: G) wts c -> (* TODO: update [wts] *) *)
    (* has_tyQual_c G wts (Let e c) *)

(* Input introduces an idempotent input-tainted value. *)
| has_tyQual_LetInput : forall tq0 G wts c,
    has_tyQual_c tq0 ((Id None, Tnt)::G) wts c -> (* TODO: update [wts] *)
    has_tyQual_c tq0 G wts (LetInput c)

(* Assignment performs a write. This only works if the incoming expression has
   an idempotence qualifier that is a subtype of the existing (which must be
   amenable to a write), and the full type qualifier must be joined.

   Comparing to the version in the paper:

     tq0 = pc
     tq1 = q_l
     tq2 = q_e
 *)
| has_tyQual_Assign : forall tq0 G wts p e tq1 tq2,
    forall qId0 qIO0, tq0 = (qId0, qIO0) ->
    forall qId1 qIO1, tq1 = (qId1, qIO1) ->
    forall qId2 qIO2, tq2 = (qId2, qIO2) ->
    idemRe qId2 qId1 ->
    forall qAcc1, idemExtractqAcc qId1 qAcc1 ->
    qAccROpt qAcc1 Wt ->
    forall tq',
    tyQualJoin tq0 tq2 tq' ->    (* TODO: Are these actually used? *)
    tyQualJoin tq1 tq' tq2 ->    (* TODO: I don't see what they're for. *)
    has_tyQual_pexp G p tq1 ->
    has_tyQual_exp G e tq2 ->
    has_tyQual_c tq0 G wts (Assign p e) (* TODO: update [wts] ??? *).

(* TODO: finish has_tyQual_c *)
