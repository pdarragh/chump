From Coq Require Import List String ZArith FSets.FMapPositive Lia.

Import ListNotations.
Local Open Scope list_scope.

From ExtLib.Structures Require Import Monad Traversable Foldable Reducible.
From ExtLib.Data Require Import List.
From ExtLib.Data.Monads Require Import OptionMonad.

Import MonadNotation.
Open Scope monad_scope.


Set Implicit Arguments.

Definition var : Type := nat.

Inductive pexp :=
| Var (x : var)
| Deref (l : pexp).

Variant op1 := Not.
Variant op2 := Plus | Minus | Mult | And | Or | Eq.

Inductive exp :=
| Int (i : Z) | Bool (b : bool)
| Ref (l : pexp)
| Load (l : pexp)
| Op1 (o : op1) (e : exp)
| Op2 (o : op2) (e1 : exp) (e2 : exp).

Inductive c :=
| Noop
| Let (e : exp) (body : c)
| LetInput (body : c)
| Assign (l : pexp) (e : exp)
| If (e : exp) (thn: c) (els : c)
| Loop (body : c)
| Break (n : nat)
| Output (e : exp)
| Seq (s1 : c) (s2 : c)
| Checkpoint (ls : list pexp).

Definition addr := positive.

(*
Inductive env A :=
| Top (f : list A)
| Frame (f : list A) (rst : env A).

Definition extend_frame {A} (fr : env A) v :=
  match fr with
  | Top l => Top (v :: l)
  | Frame l E => Frame (v :: l) E
  end.

Fixpoint lookup_frame {A} (e : env A) n : option (list A) :=
  match n, e with
  | 0, Top f | 0, Frame f _ => Some f
  | S n, Frame _ rst => lookup_frame rst n
  | S _, Top _ => None
  end.

Definition lookup_env {A} (e : env A) (v : var) : option A :=
  let '(i, j) := v in
  f <- lookup_frame e i ;;
  nth_error f j.
*)

Definition env := list.
Definition lookup_env := nth_error.

Inductive val :=
| vInt (i : Z)
| vBool (b : bool)
| vPtr (p : addr).

Record store := mkStore { st_next : positive ; st_map : PositiveMap.t val }.

Definition lookup_store (s : store) (a : addr) :=
  PositiveMap.find a (st_map s).

Definition store_add (s : store) (a : addr) (v : val) :=
  mkStore (st_next s) (PositiveMap.add a v (st_map s)).

Definition store_add_next (s : store) (v : val) :=
  mkStore (Pos.succ (st_next s)) (PositiveMap.add (st_next s) v (st_map s)).

Definition init_store := mkStore xH (PositiveMap.empty val).

Definition store_wf (s : store) :=
  forall a, (st_next s <= a)%positive -> PositiveMap.find a (st_map s) = None.

Lemma init_store_wf : store_wf init_store.
Proof.
  unfold store_wf, init_store.
  cbn.
  intros.
  apply PositiveMap.gempty.
Qed.

Lemma store_wf_add_next_wf : forall s v, store_wf s -> store_wf (store_add_next s v).
Proof.
  unfold store_wf, store_add_next.
  cbn.
  intros s v H a Hle.
  rewrite PositiveMapAdditionalFacts.gsspec.
  destruct (PositiveMap.E.eq_dec a (st_next s)).
  - lia.
  - apply H. lia.
Qed.

Inductive kont :=
| kMt
| kSeq (s2 : c) (E : env addr) (k : kont)
| kLoop (body : c) (E : env addr) (k : kont).

Fixpoint eval_pexp E St p : option addr :=
  match p with
  | Var x => lookup_env E x
  | Deref p =>
    l <- eval_pexp E St p ;;
    v <- lookup_store St l ;;
    match v with
    | vPtr p => ret p
    | _ => None
    end
  end.

Definition eval_op1 o v : option val :=
  match o, v with
  | Not, vBool b => ret (vBool (negb b))
  | _, _ => None
  end.

Definition eval_op2 o v1 v2 : option val :=
  match o, v1, v2 with
  | Plus, vInt i1, vInt i2 => ret (vInt (i1 + i2))
  | Minus, vInt i1, vInt i2 => ret (vInt (i1 - i2))
  | Mult, vInt i1, vInt i2 => ret (vInt (i1 * i2))
  | And, vBool b1, vBool b2 => ret (vBool (b1 && b2))
  | Or, vBool b1, vBool b2 => ret (vBool (b1 || b2))
  | Eq, vInt i1, vInt i2 => ret (vBool (i1 =? i2)%Z)
  | Eq, vPtr a1, vPtr a2 => ret (vBool (a1 =? a2)%positive)
  | _, _, _ => None
  end.

Fixpoint eval (E : env addr) (St : store) (e : exp) : option val :=
  match e with
  | Int i => ret (vInt i)
  | Bool b => ret (vBool b)
  | Ref p =>
    ptr <- eval_pexp E St p ;;
    ret (vPtr ptr)
  | Load p =>
    ptr <- eval_pexp E St p ;;
    lookup_store St ptr
  | Op1 o e =>
    v <- eval E St e ;;
    eval_op1 o v
  | Op2 o e1 e2 =>
    v1 <- eval E St e1 ;;
    v2 <- eval E St e2 ;;
    eval_op2 o v1 v2
  end.

Fixpoint do_break n k : option kont :=
  match k with
  | kSeq _ _ k => do_break n k
  | kLoop _ _ k =>
    match n with
    | 0 => Some k
    | S n => do_break n k
    end
  | kMt => None
  end.

Definition checkpoint : Type := kont * list (addr * val).
Definition CESKP : Type := c * env addr * store * kont * checkpoint.

Variant event :=
| ePure (st : CESKP)
| eInput (f : Z -> CESKP)
| eOutput (o : Z) (st : CESKP)
| eCheckpoint (st : CESKP).



Definition next (st : CESKP) : option event :=
  let '(s, E, St, k, P) := st in
  match s return option event with
  | Let e body =>
    v <- eval E St e ;;
    ret (ePure (body, st_next St :: E, store_add_next St v, k, P))
  | LetInput body =>
    ret (eInput (fun i => (body, st_next St :: E, store_add_next St (vInt i), k, P)))
  | Assign l e =>
    v <- eval E St e ;;
    ptr <- eval_pexp E St l ;;
    Some (ePure (Noop, E, store_add St ptr v, k, P))
  | If e s1 s2 =>
    v <- eval E St e ;;
    match v with
    | vBool b => ret (ePure (if b then s1 else s2, E, St, k, P))
    | _ => None
    end
  | Loop s => ret (ePure (s, E, St, kLoop s E k, P))
  | Break n =>
    k' <- do_break n k ;;
    ret (ePure (Noop, E, St, k', P))
  | Seq s1 s2 => ret (ePure (s1, E, St, kSeq s2 E k, P))

  | Noop =>
    match k with
    | kSeq s2 E' k' => ret (ePure (s2, E', St, k', P))
    | kLoop s' E' k' => ret (ePure (s', E', St, kLoop s' E' k', P))
    | kMt => None
    end

  | Output e =>
    v <- eval E St e ;;
    match v with
    | vInt i => ret (eOutput i (Noop, E, St, k, P))
    | _ => None
    end

  | Checkpoint ps =>
    ls <- mapT (eval_pexp E St) ps ;;
    vs <- mapT (lookup_store St) ls ;;
    ret (eCheckpoint (Noop, E, St, k, (k, combine ls vs)))
  end.

Definition do_reset (st : CESKP) : CESKP :=
  let '(_, _, St, _, (k, chks)) := st in
  let St' := fold (fun '(a, v) St' => store_add St' a v) St chks in
  (Noop, [], St', k, (k, chks)).

(* IO log, allows for nondeterminism w/ still reasoning about what inputs were seen/are the same *)

Variant io_event :=
| io_in (i : Z)
| io_out (i : Z)
| io_check
| io_reset.

Definition io_log := list io_event.

Definition state : Type := CESKP * io_log.

Inductive step : state -> state -> Prop :=
| step_Let : forall e c E St k P io v,
  eval E St e = Some v ->
  step ((Let e c, E, St, k, P), io)
       ((c, st_next St :: E, store_add_next St v, k, P), io)

| step_LetInput : forall c E St k P io i,
  step ((LetInput c, E, St, k, P), io)
       ((c, st_next St :: E, store_add_next St (vInt i), k, P), io_in i :: io)

| step_Assign : forall p e E St k P io v a,
  eval E St e = Some v ->
  eval_pexp E St p = Some a ->
  step ((Assign p e, E, St, k, P), io)
       ((Noop, E, store_add St a v, k, P), io)

| step_If_true : forall e c1 c2 E St k P io,
  eval E St e = Some (vBool true) ->
  step ((If e c1 c2, E, St, k, P), io)
       ((c1, E, St, k, P), io)

| step_If_false : forall e c1 c2 E St k P io,
  eval E St e = Some (vBool false) ->
  step ((If e c1 c2, E, St, k, P), io)
       ((c2, E, St, k, P), io)

| step_Loop : forall c E St k P io,
  step ((Loop c, E, St, k, P), io)
       ((c, E, St, kLoop c E k, P), io)

| step_kLoop : forall E' St c E k P io,
  step ((Noop, E', St, kLoop c E k, P), io)
       ((c, E, St, kLoop c E k, P), io)

| step_Break : forall n E St k P io k',
  do_break n k = Some k' ->
  step ((Break n, E, St, k, P), io)
       ((Noop, E, St, k', P), io)

| step_Output : forall e E St k P io i,
  eval E St e = Some (vInt i) ->
  step ((Output e, E, St, k, P), io)
       ((Noop, E, St, k, P), io_out i :: io)

| step_Seq : forall c1 c2 E St k P io,
  step ((Seq c1 c2, E, St, k, P), io)
       ((c1, E, St, kSeq c2 E k, P), io)

| step_kSeq : forall E' St c2 E k P io,
  step ((Noop, E', St, kSeq c2 E k, P), io)
       ((c2, E, St, k, P), io)

| step_Checkpoint : forall ps E St k P io chks,
  Forall2 (fun p '(a, v) => eval_pexp E St p = Some a /\ lookup_store St a = Some v) ps chks ->
  step ((Checkpoint ps, E, St, k, P), io)
       ((Noop, E, St, k, (k, chks)), io_reset :: io).

Fixpoint filter_log l :=
  match l with
  | [] => []
  | io_in v :: l' => io_in v :: filter_log l'
  | io_out v :: l' => io_out v :: filter_log l'
  | io_check :: l' => io_check :: filter_log l'
  | io_reset :: l' => remove_reset l'
  end
with remove_reset l :=
  match l with
  | [] => []
  | io_check :: l' => io_check :: filter_log l'
  | _ :: l' => remove_reset l'
  end.

Inductive ty := tInt | tBool | tPtr (t : ty).

Inductive has_ty_pexp : env ty -> pexp -> ty -> Prop :=
| has_ty_Var : forall G x t,
  lookup_env G x = Some t ->
  has_ty_pexp G (Var x) t
| has_ty_Deref : forall G p t,
  has_ty_pexp G p (tPtr t) ->
  has_ty_pexp G (Deref p) t.

Variant has_ty_op1 : op1 -> ty -> ty -> Prop :=
| has_ty_Not : has_ty_op1 Not tBool tBool.

Variant has_ty_op2 : op2 -> ty -> ty -> ty -> Prop :=
| has_ty_Plus : has_ty_op2 Plus tInt tInt tInt
| has_ty_Minus : has_ty_op2 Minus tInt tInt tInt
| has_ty_Mult : has_ty_op2 Mult tInt tInt tInt
| has_ty_And : has_ty_op2 And tBool tBool tBool
| has_ty_Or : has_ty_op2 Or tBool tBool tBool
| has_ty_Eq_Int : has_ty_op2 Eq tInt tInt tBool
| has_ty_Eq_Ptr : forall t, has_ty_op2 Eq (tPtr t) (tPtr t) tBool.

Inductive has_ty_exp : env ty -> exp -> ty -> Prop :=
| has_ty_Int : forall G i, has_ty_exp G (Int i) tInt
| has_ty_Bool : forall G b, has_ty_exp G (Bool b) tBool
| has_ty_Ref : forall G p t,
  has_ty_pexp G p t ->
  has_ty_exp G (Ref p) (tPtr t)
| has_ty_Load : forall G p t,
  has_ty_pexp G p t ->
  has_ty_exp G (Load p) t

| has_ty_Op1 : forall G o e t1 t2,
  has_ty_op1 o t1 t2 ->
  has_ty_exp G e t1 ->
  has_ty_exp G (Op1 o e) t2

| has_ty_Op2 : forall G o e1 e2 t1 t2 t3,
  has_ty_op2 o t1 t2 t3 ->
  has_ty_exp G e1 t1 ->
  has_ty_exp G e2 t2 ->
  has_ty_exp G (Op2 o e1 e2) t3.

Inductive has_ty_c : env ty -> nat -> c -> Prop :=
| has_ty_Noop : forall G n, has_ty_c G n Noop
| has_ty_Let : forall G n e t c,
  has_ty_exp G e t ->
  has_ty_c (t :: G) n c ->
  has_ty_c G n (Let e c)
| has_ty_LetInput : forall G n c,
  has_ty_c (tInt :: G) n c ->
  has_ty_c G n (LetInput c)
| has_ty_Assign : forall G n p e t,
  has_ty_pexp G p t ->
  has_ty_exp G e t ->
  has_ty_c G n (Assign p e)

| has_ty_If : forall G n e c1 c2,
  has_ty_exp G e tBool ->
  has_ty_c G n c1 ->
  has_ty_c G n c2 ->
  has_ty_c G n (If e c1 c2)

| has_ty_Loop : forall G n c,
  has_ty_c G (S n) c ->
  has_ty_c G n (Loop c)

| has_ty_Break : forall G n m,
  m < n ->
  has_ty_c G n (Break m)

| has_ty_Output : forall G n e,
  has_ty_exp G e tInt ->
  has_ty_c G n (Output e)

| has_ty_Seq : forall G n c1 c2,
  has_ty_c G n c1 ->
  has_ty_c G n c2 ->
  has_ty_c G n (Seq c1 c2)

| has_ty_Checkpoint : forall G n ps ts,
  Forall2 (has_ty_pexp G) ps ts ->
  has_ty_c G n (Checkpoint ps).



Inductive has_ty_val (St : store) : val -> ty -> Prop :=
| has_ty_vInt : forall i, has_ty_val St (vInt i) tInt
| has_ty_vBool : forall b, has_ty_val St (vBool b) tBool
| has_ty_vPtr : forall a v t,
  lookup_store St a = Some v ->
  has_ty_val St v t ->
  has_ty_val St (vPtr a) (tPtr t).

Definition has_ty_env (St : store) := Forall2 (fun a t => has_ty_val St (vPtr a) (tPtr t)).

Inductive has_ty_kont : nat -> kont -> Prop :=
| has_ty_kMt : has_ty_kont 0 kMt
| has_ty_kSeq : forall G n c2 E k,
  (forall St, has_ty_env St E G -> has_ty_c G n c2) ->
  has_ty_kont n k ->
  has_ty_kont n (kSeq c2 E k)
| has_ty_kLoop : forall G n c E k,
  (forall St, has_ty_env St E G -> has_ty_c G (S n) c) ->
  has_ty_kont n (kLoop c E k).



Lemma Forall2_nth_error_1 : forall {A B} P (l1 : list A) (l2 : list B),
  Forall2 P l1 l2 ->
  forall n x,
  nth_error l1 n = Some x ->
  exists y, nth_error l2 n = Some y /\ P x y.
Proof.
  intros A B P l1 l2 Hforall.
  induction Hforall; intros n z Hnth.
  - destruct n; discriminate.
  - destruct n; cbn in *.
    + exists y.
      split; [reflexivity|].
      injection Hnth as Heq.
      rewrite <- Heq.
      apply H.
    + apply IHHforall, Hnth.
Qed.

Lemma Forall2_nth_error_2 : forall {A B} P (l1 : list A) (l2 : list B),
  Forall2 P l1 l2 ->
  forall n y,
  nth_error l2 n = Some y ->
  exists x, nth_error l1 n = Some x /\ P x y.
Proof.
  intros ? ? ? ? ? Hforall.
  apply Forall2_nth_error_1, Forall2_flip, Hforall.
Qed.



Lemma well_typed_eval_pexp : forall G t E St p,
  has_ty_env St E G ->
  has_ty_pexp G p t ->
  exists a v, eval_pexp E St p = Some a /\ lookup_store St a = Some v /\ has_ty_val St v t.
Proof.
  intros G t E St p Henv.
  generalize dependent t.
  induction p; intros t Hty; inversion Hty; subst.
  - cbn.
    unfold has_ty_env in Henv.
    apply (Forall2_nth_error_2 Henv) in H1 as [a [Hnth Htyv]].
    inversion Htyv; subst.
    eauto.
  - cbn.
    apply IHp in H1 as [a [v [Heval [Hlookup Htyv]]]].
    rewrite Heval, Hlookup.
    inversion Htyv; subst.
    eauto.
Qed.

Lemma well_typed_eval : forall G t E St e,
  has_ty_env St E G ->
  has_ty_exp G e t ->
  exists v, eval E St e = Some v /\ has_ty_val St v t.
Proof.
  intros G t E St e Henv.
  generalize dependent t.
  induction e; intros t Hty; inversion Hty; subst.
  - cbn. eexists; split; eauto; constructor.
  - cbn. eexists; split; eauto; constructor.
  - apply (well_typed_eval_pexp Henv) in H1 as [a [v [Heval [Hlookup Htyv]]]].
    cbn.
    rewrite Heval.
    eexists; split; eauto.
    econstructor; eassumption.
  - apply (well_typed_eval_pexp Henv) in H1 as [a [v [Heval [Hlookup Htyv]]]].
    cbn.
    rewrite Heval.
    eexists; eauto.
  - inversion H0; subst.
    destruct o.
    cbn.
    apply IHe in H2 as [v [Heval Htyv]].
    rewrite Heval.
    inversion Htyv; subst.
    eexists; split; eauto; constructor.
  - cbn.
    apply IHe1 in H5 as [v1 [Heval1 Htyv1]].
    rewrite Heval1.
    apply IHe2 in H6 as [v2 [Heval2 Htyv2]].
    rewrite Heval2.
    inversion H3; subst; inversion Htyv1; inversion Htyv2; subst; cbn;
    eexists; split; eauto; constructor.
Qed.

Inductive has_ty_CESKP : CESKP -> Prop :=
| has_ty_ceskp : forall G n c E St k P,
  has_ty_env St E G ->
  has_ty_c G n c ->
  has_ty_kont n k ->
  has_ty_CESKP (c, E, St, k, P).

Lemma preservation : forall st st' io io',
  has_ty_CESKP st ->
  step (st, io) (st', io') ->
  has_ty_CESKP st'.
Proof.
  intros st st' io io' Hty Hstep.
  destruct st as [[[[c E] St] k] P].
  destruct st' as [[[[c' E'] St'] k'] P'].
  inversion Hstep; subst; admit.
Abort.
