From Coq Require Import List String ZArith FSets.FMapPositive Lia.

Import ListNotations.
Local Open Scope list_scope.

From ExtLib.Structures Require Import Monad Traversable Foldable Reducible.
From ExtLib.Data Require Import List.
From ExtLib.Data.Monads Require Import OptionMonad.

Import MonadNotation.
Open Scope monad_scope.


Set Implicit Arguments.

Definition var : Type := nat * nat.

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

Inductive val :=
| vInt (i : Z)
| vBool (b : bool)
| vPtr (p : addr)
| vNull.

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
| kEndIf (k : kont)
| kSeq (s2 : c) (k : kont)
| kLoop (body : c) (k : kont).

(*
Definition update_rev_nth {A} (l : list A) n v := rev (firstn n (rev l) ++ [v] ++ skipn (S n) (rev l)).
Definition rev_nth_error {A} (l : list A) n := nth_error (rev l) n.
*)

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

Fixpoint do_break n E k : option (env addr * kont) :=
  match k, E with
  | kEndIf k, Frame _ E => do_break n E k
  | kSeq _ k, Frame _ E => do_break n E k
  | kLoop _ k, Frame _ E =>
    match n with
    | 0 => ret (E, k)
    | S n => do_break n E k
    end
  | kMt, _ | _, Top _ => None
  end.

Definition CESK : Type := c * env addr * store * kont.
Definition checkpoint : Type := env addr * kont * list (addr * val).

Variant event :=
| ePure (st : CESK)
| eInput (f : Z -> CESK)
| eOutput (o : Z) (st : CESK)
| eCheckpoint (chkp : checkpoint) (st : CESK).



Definition next (st : CESK) : option event :=
  let '(s, E, St, k) := st in
  match s return option event with
  | Let e body =>
    v <- eval E St e ;;
    ret (ePure (body,
                extend_frame E (st_next St),
                store_add_next St v,
                k))
  | LetInput body =>
    ret (eInput (fun i => (body, extend_frame E (st_next St),
                           store_add_next St (vInt i), k)))
  | Assign l e =>
    v <- eval E St e ;;
    ptr <- eval_pexp E St l ;;
    Some (ePure (Noop, E, store_add St ptr v, k))
  | If e s1 s2 =>
    v <- eval E St e ;;
    match v with
    | vBool b => ret (ePure (if b then s1 else s2, E, St, kEndIf k))
    | _ => None
    end
  | Loop s => ret (ePure (s, Frame [] E, St, kLoop s k))
  | Break n =>
    '(E', k') <- do_break n E k ;;
    ret (ePure (Noop, E', St, k'))
  | Seq s1 s2 => ret (ePure (s1, Frame [] E, St, kSeq s2 k))

  | Noop =>
    match k, E with
    | kEndIf k', Frame _ E' => ret (ePure (Noop, E', St, k'))
    | kSeq s2 k', Frame _ E' => ret (ePure (s2, E', St, k'))
    | kLoop s' k', Frame _ E' => ret (ePure (s', Frame [] E', St, kLoop s' k'))
    | kMt, _ | _, Top _ => None
    end

  | Output e =>
    v <- eval E St e ;;
    match v with
    | vInt i => ret (eOutput i (Noop, E, St, k))
    | _ => None
    end

  | Checkpoint ps =>
    ls <- mapT (eval_pexp E St) ps ;;
    vs <- mapT (lookup_store St) ls ;;
    ret (eCheckpoint (E, k, combine ls vs) (Noop, E, St, k))
  end.

Definition do_reset (st : CESK) (p : checkpoint) : CESK :=
  let '(_, _, St, _) := st in
  let '(E, k, chks) := p in
  let St' := fold (fun '(a, v) St' => store_add St' a v) St chks in
  (Noop, E, St', k).

(* IO log, allows for nondeterminism w/ still reasoning about what inputs were seen/are the same *)

Variant io_event :=
| io_in (i : Z)
| io_out (i : Z)
| io_check
| io_reset.

Definition io_log := list io_event.

Definition state : Type := CESK * checkpoint * io_log.

Inductive step : state -> state -> Prop :=
| step_pure : forall c1 c2 p io,
  next c1 = Some (ePure c2) ->
  step (c1, p, io) (c2, p, io)
| step_input : forall c1 f i p io,
  next c1 = Some (eInput f) ->
  step (c1, p, io) (f i, p, io_in i :: io)
| step_output : forall c1 c2 i p io,
  next c1 = Some (eOutput i c2) ->
  step (c1, p, io) (c2, p, io_out i :: io)
| step_check : forall c1 c2 p p' io,
  next c1 = Some (eCheckpoint p c2) ->
  step (c1, p', io) (c2, p, io_check :: io)
| step_reset : forall c1 p io,
  step (c1, p, io) (do_reset c1 p, p, io_reset :: io).

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
  has_ty_c (extend_frame G t) n c ->
  has_ty_c G n (Let e c)
| has_ty_LetInput : forall G n c,
  has_ty_c (extend_frame G tInt) n c ->
  has_ty_c G n (LetInput c)
| has_ty_Assign : forall G n p e t,
  has_ty_pexp G p t ->
  has_ty_exp G e t ->
  has_ty_c G n (Assign p e)

| has_ty_If : forall G n e c1 c2,
  has_ty_exp G e tBool ->
  has_ty_c (Frame [] G) n c1 ->
  has_ty_c (Frame [] G) n c2 ->
  has_ty_c G n (If e c1 c2)

| has_ty_Loop : forall G n c,
  has_ty_c (Frame [] G) (S n) c ->
  has_ty_c G n (Loop c)

| has_ty_Break : forall G n m,
  m < n ->
  has_ty_c G n (Break m)

| has_ty_Output : forall G n e,
  has_ty_exp G e tInt ->
  has_ty_c G n (Output e)

| has_ty_Seq : forall G n c1 c2,
  has_ty_c (Frame [] G) n c1 ->
  has_ty_c G n c2 ->
  has_ty_c G n (Seq c1 c2)

| has_ty_Checkpoint : forall G n ps ts,
  Forall2 (has_ty_pexp G) ps ts ->
  has_ty_c G n (Checkpoint ps).

