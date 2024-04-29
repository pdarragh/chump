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

Definition env := list.
Definition lookup_env := nth_error.

Inductive val :=
| vInt (i : Z)
| vBool (b : bool)
| vPtr (p : addr).

Record store A := mkStore { st_next : positive ; st_map : PositiveMap.t A }.

Definition lookup_store {A} (s : store A) (a : addr) :=
  PositiveMap.find a (st_map s).

Definition store_add {A} (s : store A) (a : addr) (v : A) :=
  mkStore (Pos.max (st_next s) (Pos.succ a)) (PositiveMap.add a v (st_map s)).

Definition init_store {A} := mkStore xH (PositiveMap.empty A).

Definition store_wf {A} (s : store A) :=
  forall a, (st_next s <= a)%positive -> PositiveMap.find a (st_map s) = None.

Lemma init_store_wf : forall {A}, @store_wf A init_store.
Proof.
  unfold store_wf, init_store.
  cbn.
  intros.
  apply PositiveMap.gempty.
Qed.

Lemma store_wf_add_wf : forall {A} (s : store A) a v,
  store_wf s -> store_wf (store_add s a v).
Proof.
  unfold store_wf, store_add.
  cbn.
  intros A s a v Hwf a' Hle.
  rewrite PositiveMapAdditionalFacts.gsspec.
  destruct (PositiveMap.E.eq_dec a' a).
  - lia.
  - apply Hwf.
    lia.
Qed.

Lemma store_wf_lookup_lt : forall {A} (s : store A) a v,
  store_wf s -> lookup_store s a = Some v -> (a < st_next s)%positive.
Proof.
  unfold store_wf, lookup_store.
  intros A s a v Hwf Hfind.
  destruct (st_next s <=? a)%positive eqn:E.
  - apply Pos.leb_le, Hwf in E.
    rewrite E in Hfind.
    discriminate.
  - apply Pos.leb_gt, E.
Qed.

Lemma lookup_store_add_neq : forall A (s : store A) a a' v',
  a <> a' ->
  lookup_store (store_add s a' v') a = lookup_store s a.
Proof.
  unfold lookup_store, store_add.
  cbn.
  intros A s a a' v' Hneq.
  rewrite PositiveMapAdditionalFacts.gsspec.
  destruct (PositiveMap.E.eq_dec a a').
  - contradiction.
  - reflexivity.
Qed.

Lemma lookup_store_add_eq : forall A (s : store A) a v,
  lookup_store (store_add s a v) a = Some v.
Proof.
  unfold lookup_store, store_add.
  cbn.
  intros.
  rewrite PositiveMapAdditionalFacts.gsspec.
  destruct (PositiveMap.E.eq_dec a a).
  - reflexivity.
  - contradiction.
Qed.

Lemma store_add_idemp : forall A (s : store A) a v,
  store_wf s ->
  lookup_store s a = Some v ->
  store_add s a v = s.
Proof.
  unfold lookup_store, store_add.
  intros A s a v Hwf Hfind.
  assert (a < st_next s)%positive by eauto using store_wf_lookup_lt.
  replace (Pos.max (st_next s) (Pos.succ a)) with (st_next s) by lia.
  rewrite PositiveMapAdditionalFacts.gsident by auto.
  destruct s.
  reflexivity.
Qed.

Corollary store_wf_next_None : forall A (s : store A),
  store_wf s ->
  lookup_store s (st_next s) = None.
Proof.
  unfold store_wf, lookup_store.
  intros A s H.
  apply H.
  reflexivity.
Qed.

Global Hint Rewrite
  lookup_store_add_neq lookup_store_add_eq store_add_idemp store_wf_next_None : core.
Global Hint Resolve
  store_wf_add_wf store_wf_lookup_lt lookup_store_add_eq store_wf_next_None : core.
Global Hint Immediate lookup_store_add_eq store_wf_next_None : core.


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

Fixpoint eval (E : env addr) (St : store val) (e : exp) : option val :=
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
Definition CESKP : Type := c * env addr * store val * kont * checkpoint.

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
    ret (ePure (body, st_next St :: E, store_add St (st_next St) v, k, P))
  | LetInput body =>
    ret (eInput (fun i => (body, st_next St :: E, store_add St (st_next St) (vInt i), k, P)))
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

Definition do_reset : store val -> list (addr * val) -> store val :=
  fold (fun '(a, v) St' => store_add St' a v).

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
       ((c, st_next St :: E, store_add St (st_next St) v, k, P), io)

| step_LetInput : forall c E St k P io i,
  step ((LetInput c, E, St, k, P), io)
       ((c, st_next St :: E, store_add St (st_next St) (vInt i), k, P), io_in i :: io)

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
       ((Noop, E, St, k, (k, chks)), io_check :: io)

| step_Reset : forall c E St k' k chks io,
  step ((c, E, St, k', (k, chks)), io)
       ((Noop, [], do_reset St chks, k, (k, chks)), io_reset :: io).

Global Hint Constructors step : core.

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

Definition initial_state c : CESKP := (c, [], init_store, kMt, (kSeq c [] kMt, [])).

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

Global Hint Constructors has_ty_pexp has_ty_op1 has_ty_op2 has_ty_exp has_ty_c : core.



Variant has_ty_val (ST : store ty) : val -> ty -> Prop :=
| has_ty_vInt : forall i, has_ty_val ST (vInt i) tInt
| has_ty_vBool : forall b, has_ty_val ST (vBool b) tBool
| has_ty_vPtr : forall a t,
  lookup_store ST a = Some t ->
  has_ty_val ST (vPtr a) (tPtr t).

Definition has_ty_env (ST : store ty) := Forall2 (fun a t => has_ty_val ST (vPtr a) (tPtr t)).

Variant has_ty_store St ST :=
| has_ty_st :
  store_wf St ->
  store_wf ST ->
  (st_next ST <= st_next St)%positive ->
  (forall a t,
    lookup_store ST a = Some t ->
    exists v, lookup_store St a = Some v /\ has_ty_val ST v t) ->
  has_ty_store St ST.

Inductive has_ty_kont (ST : store ty) : nat -> kont -> Prop :=
| has_ty_kMt : has_ty_kont ST 0 kMt
| has_ty_kSeq : forall G n c2 E k,
  has_ty_env ST E G ->
  has_ty_c G n c2 ->
  has_ty_kont ST n k ->
  has_ty_kont ST n (kSeq c2 E k)
| has_ty_kLoop : forall G n c E k,
  has_ty_env ST E G ->
  has_ty_c G (S n) c ->
  has_ty_kont ST n k ->
  has_ty_kont ST (S n) (kLoop c E k).

Inductive has_ty_checkpoint (ST : store ty) : checkpoint -> Prop :=
| has_ty_P : forall n k chks ts,
  Forall2 (fun '(a, v) t => has_ty_val ST (vPtr a) (tPtr t) /\ has_ty_val ST v t) chks ts ->
  has_ty_kont ST n k ->
  has_ty_checkpoint ST (k, chks).

Inductive has_ty_CESKP : CESKP -> Prop :=
| has_ty_ceskp : forall G n ST c E St k P,
  has_ty_c G n c ->
  has_ty_env ST E G ->
  has_ty_store St ST ->
  has_ty_kont ST n k ->
  has_ty_checkpoint ST P ->
  has_ty_CESKP (c, E, St, k, P).

Global Hint Unfold has_ty_env : core.
Global Hint Constructors has_ty_val has_ty_store has_ty_kont has_ty_CESKP : core.

Lemma has_ty_env_store_add_new : forall ST a t E G,
  store_wf ST ->
  lookup_store ST a = None ->
  has_ty_env ST E G ->
  has_ty_env (store_add ST a t) E G.
Proof.
  unfold has_ty_env.
  intros s a t E G Hwf Hlookup Henv.
  eapply Forall2_impl; [|apply Henv].
  cbn.
  intros a' t' Htyv.
  inversion Htyv; subst.
  constructor; eauto.
  destruct (Pos.eq_dec a a').
  - subst.
    rewrite H1 in Hlookup.
    discriminate.
  - rewrite lookup_store_add_neq; auto.
Qed.

Lemma has_ty_val_store_add : forall ST a t t' v,
  lookup_store ST a = None ->
  has_ty_val ST v t' ->
  has_ty_val (store_add ST a t) v t'.
Proof.
  intros ST a t t' v Hlookup Htyv.
  induction Htyv; auto.
  constructor.
  destruct (Pos.eq_dec a a0).
  - subst.
    rewrite H in Hlookup.
    discriminate.
  - rewrite lookup_store_add_neq; auto.
Qed.

Lemma has_ty_env_add_var : forall s a t E G,
  has_ty_val s (vPtr a) (tPtr t) ->
  has_ty_env s E G ->
  has_ty_env s (a :: E) (t :: G).
Proof.
  intros.
  constructor; auto.
Qed.

Lemma has_ty_store_add : forall St ST a v t,
  has_ty_store St ST ->
  lookup_store ST a = Some t ->
  has_ty_val ST v t ->
  has_ty_store (store_add St a v) ST.
Proof.
  intros St ST a v t Hstore Hlookup Htyv.
  inversion Hstore; subst.
  assert (a < st_next ST)%positive by eauto.
  assert (a < st_next St)%positive by lia.
  econstructor; eauto.
  - unfold store_add. cbn. lia.
  - intros a' t' Hlookup'.
    destruct (Pos.eq_dec a a').
    + subst.
      exists v.
      split; auto.
      rewrite Hlookup' in Hlookup.
      injection Hlookup as Heq.
      subst.
      assumption.
    + apply H2 in Hlookup' as [v' [Hlookup' Htyv']].
      exists v'.
      rewrite lookup_store_add_neq; auto.
Qed.

Lemma has_ty_store_add_new : forall St ST a v t,
  has_ty_store St ST ->
  has_ty_val ST v t ->
  lookup_store ST a = None ->
  has_ty_store (store_add St a v) (store_add ST a t).
Proof.
  intros St ST a v t Hstore Htyv Hlookup.
  inversion Hstore; subst.
  econstructor; eauto.
  - unfold store_add. cbn. lia.
  - intros a' t' Hlookup'.
    destruct (Pos.eq_dec a a').
    + subst.
      eexists; split; eauto.
      rewrite lookup_store_add_eq in Hlookup'.
      injection Hlookup' as ?; subst.
      apply has_ty_val_store_add; auto.
    + rewrite lookup_store_add_neq in Hlookup'; auto.
      apply H2 in Hlookup' as [? [? ?]].
      eexists. split.
      * rewrite lookup_store_add_neq; eauto.
      * apply has_ty_val_store_add; eauto.
Qed.

Global Hint Resolve
  has_ty_val_store_add
  has_ty_env_store_add_new
  has_ty_store_add
  has_ty_store_add_new
  has_ty_env_add_var : core.

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



Lemma well_typed_eval_pexp : forall G ST t E St p,
  has_ty_store St ST ->
  has_ty_env ST E G ->
  has_ty_pexp G p t ->
  exists a, eval_pexp E St p = Some a /\ lookup_store ST a = Some t.
Proof.
  intros G ST t E St p Hstore Henv.
  generalize dependent t.
  induction p; intros t Hty; inversion Hty; subst.
  - cbn.
    unfold has_ty_env in Henv.
    apply (Forall2_nth_error_2 Henv) in H1 as [a [Hnth Htyv]].
    inversion Htyv; subst.
    eauto.
  - cbn.
    apply IHp in H1 as [a [Heval Hlookup]].
    apply Hstore in Hlookup as [? [Hlookup Htyv]].
    rewrite Heval, Hlookup.
    inversion Htyv; subst.
    eauto.
Qed.

Lemma well_typed_eval : forall G ST t E St e,
  has_ty_store St ST ->
  has_ty_env ST E G ->
  has_ty_exp G e t ->
  exists v, eval E St e = Some v /\ has_ty_val ST v t.
Proof.
  intros G ST t E St e Hstore Henv.
  generalize dependent t.
  induction e; intros t Hty; inversion Hty; subst; cbn; eauto.
  - apply (well_typed_eval_pexp Hstore Henv) in H1 as [a [Heval Hlookup]].
    rewrite Heval.
    eauto.
  - apply (well_typed_eval_pexp Hstore Henv) in H1 as [a [Heval Hlookup]].
    apply Hstore in Hlookup as [? [Hlookup Htyv]].
    rewrite Heval.
    eauto.
  - inversion H0; subst.
    destruct o.
    cbn.
    apply IHe in H2 as [v [Heval Htyv]].
    rewrite Heval.
    inversion Htyv; subst.
    eauto.
  - cbn.
    apply IHe1 in H5 as [v1 [Heval1 Htyv1]].
    rewrite Heval1.
    apply IHe2 in H6 as [v2 [Heval2 Htyv2]].
    rewrite Heval2.
    inversion H3; subst; inversion Htyv1; inversion Htyv2; subst; cbn; eauto.
Qed.

Lemma well_typed_break : forall St n m k,
  has_ty_kont St n k ->
  m < n ->
  exists o k', do_break m k = Some k' /\ has_ty_kont St o k'.
Proof.
  intros St n m k Hty.
  generalize dependent m.
  induction Hty; intros m Hlt.
  - lia.
  - apply IHHty in Hlt as [? [? [? ?]]].
    eauto.
  - destruct m; cbn.
    + eauto.
    + apply Nat.succ_lt_mono, IHHty in Hlt as [? [? [? ?]]].
      eauto.
Qed.

Lemma exists_curry : forall {A B} (P : A -> B -> Prop),
  (exists x y, P x y) <-> (exists '(x, y), P x y).
Proof.
  intros.
  split.
  - intros [x [y H]].
    exists (x, y).
    apply H.
  - intros [[x y] H].
    exists x, y.
    apply H.
Qed.

Lemma Forall2_impl_exists : forall {X Y Z} (P : X -> Y -> Prop) (Q : X -> Z -> Prop) xs ys,
  (forall x y, P x y -> exists z, Q x z) ->
  Forall2 (fun x y => P x y) xs ys ->
  exists zs, Forall2 (fun x z => Q x z) xs zs.
Proof.
  intros X Y Z P Q xs ys H HForall2.
  induction HForall2.
  - exists []. auto.
  - apply H in H0 as [z HQ].
    destruct IHHForall2 as [zs IHHForall2].
    exists (z :: zs).
    auto.
Qed.

Variant is_halted : CESKP -> Prop :=
| halted : forall E St P, is_halted (Noop, E, St, kMt, P).

Lemma progress : forall st1 io1,
  has_ty_CESKP st1 ->
  is_halted st1 \/ exists st2 io2, step (st1, io1) (st2, io2).
Proof.
  intros st2 io1 Hty.
  inversion Hty; subst.
  inversion H; subst.
  - (* Noop *)
    inversion H2; subst.
    + (* kMt *)
      left. constructor.
    + (* kSeq *)
      right. eauto.
    + (* kLoop *)
      right. eauto.

  - (* Let *)
    right.
    apply (well_typed_eval H1 H0) in H4 as [? [? ?]].
    eexists. eexists.
    econstructor; eauto.

  - (* LetInput *)
    right.
    eexists. exists (io_in 0 :: io1).
    eauto.

  - (* Assign *)
    right.
    apply (well_typed_eval H1 H0) in H5 as [? [? ?]].
    apply (well_typed_eval_pexp H1 H0) in H4 as [? [? ?]].
    eexists. eexists.
    econstructor; eauto.

  - (* If *)
    right.
    apply (well_typed_eval H1 H0) in H4 as [? [? ?]].
    inversion H7; subst.
    destruct b; eauto.

  - (* Loop *)
    right.
    eauto.

  - (* Break *)
    right.
    apply (well_typed_break H2) in H4 as [? [? [? ?]]].
    eexists. eexists.
    econstructor.
    eassumption.

  - (* Output *)
    right.
    apply (well_typed_eval H1 H0) in H4 as [? [? ?]].
    inversion H5; subst.
    eexists. eexists.
    econstructor; eauto.

  - (* Seq *)
    right.
    eauto.

  - (* Checkpoint *)
    right.
    eapply Forall2_impl_exists in H4.
    + destruct H4 as [? H4].
      eexists. eexists.
      econstructor.
      apply H4.
    + intros x y Htyp.
      apply exists_curry.
      apply (well_typed_eval_pexp H1 H0) in Htyp as [? [? ?]].
      apply H1 in H6 as [? [? ?]].
      eauto.
Qed.


Lemma Forall2_trans : forall {X Y Z} P Q R (xs : list X) (ys : list Y) (zs : list Z),
  (forall x y z, P x y -> Q y z -> R x z) ->
  Forall2 P xs ys ->
  Forall2 Q ys zs ->
  Forall2 R xs zs.
Proof.
  intros X Y Z P Q R xs ys zs H Hxy.
  generalize dependent zs.
  induction Hxy; intros zs Hyz; inversion Hyz; subst.
  - constructor.
  - constructor; eauto.
Qed.

Lemma preservation : forall st1 st2 io1 io2,
  has_ty_CESKP st1 ->
  step (st1, io1) (st2, io2) ->
  has_ty_CESKP st2.
Proof.
  intros st1 st2 io1 io2 Hty Hstep.
  destruct st1 as [[[[c1 E1] St1] k1] P1].
  destruct st2 as [[[[c2 E2] St2] k2] P2].
  inversion Hty; subst.
  inversion H6; subst.
  inversion Hstep; subst.
  - (* step_Let *)
    inversion H4; subst.
    apply (well_typed_eval H6 H5) in H13 as [? [? ?]].
    rewrite H9 in H3.
    injection H3 as ?; subst.
    eapply has_ty_ceskp with (ST := store_add ST (st_next St1) t); eauto.
    + admit. (* has_ty_kont store_add st_next *)
    + admit. (* has_ty_checkpoint store_add st_next *)
  - (* step_LetInput *)
    inversion H4; subst.
    eapply has_ty_ceskp with (ST := store_add ST (st_next St1) tInt); eauto.
    + admit. (* has_ty_kont store_add st_next *)
    + admit. (* has_ty_checkpoint store_add st_next *)
  - (* step_Assign *)
    inversion H4; subst.
    apply (well_typed_eval_pexp H6 H5) in H13 as [a2 [? ?]].
    rewrite H21 in H3.
    injection H3 as ?; subst.
    apply (well_typed_eval H6 H5) in H14 as [? [? ?]].
    rewrite H10 in H3.
    injection H3 as ?; subst.
    apply H2 in H9 as ?.
    destruct H3 as [? [? ?]].
    eauto.
  - (* step_If_true *)
    inversion H4; subst.
    eauto.
  - (* step_If_false *)
    inversion H4; subst.
    eauto.
  - (* step_Loop *)
    inversion H4; subst.
    eauto.
  - (* step_kLoop *)
    inversion H7; subst.
    eauto.
  - (* step_Break *)
    inversion H4; subst.
    apply (well_typed_break H7) in H12 as [? [? [? ?]]].
    rewrite H9 in H3.
    injection H3 as ?; subst.
    eauto.
  - (* step_Output *)
    eauto.
  - (* step_Seq *)
    inversion H4; subst.
    eauto.
  - (* step_kSeq *)
    inversion H7; subst.
    eauto.
  - (* step_Checkpoint *)
    inversion H4; subst.
    econstructor; eauto.
    econstructor; eauto.
    eapply Forall2_trans; [|apply Forall2_flip, H9|apply H12].
    intros [a v] p t [Heval Hlookup] Htyp.
    apply (well_typed_eval_pexp H6 H5) in Htyp as [? [? ?]].
    rewrite H3 in Heval.
    injection Heval as ?; subst.
    split; eauto.
    apply H2 in H10 as [? [? ?]].
    rewrite H10 in Hlookup.
    injection Hlookup as ?; subst.
    assumption.
  - (* step_Reset *)
    inversion H8; subst.
    econstructor; eauto.
    admit. (* has_ty_store do_reset *)
Admitted.