From Coq Require Import List String ZArith.

Import ListNotations.
Local Open Scope list_scope.

From ExtLib.Structures Require Import Monad Traversable.
From ExtLib.Data Require Import List.
From ExtLib.Data.Monads Require Import OptionMonad.

Import MonadNotation.
Open Scope monad_scope.

Require Import Map.


Set Implicit Arguments.

Definition var : Type := nat * nat.

Inductive pexp :=
| Var (x : var)
| Deref (l : pexp).

Variant op1 := Not.
Variant op2 := Plus | Minus | Mult | And | Or.

Inductive exp :=
| Int (i : Z) | Bool (b : bool)
| Ref (l : pexp)
| Load (l : pexp)
| Op1 (o : op1) (e : exp)
| Op2 (o : op2) (e1 : exp) (e2 : exp).

Inductive s :=
| Noop
| Let (e : exp) (body : s)
| LetInput (body : s)
| Assign (l : pexp) (e : exp)
| If (e : exp) (thn: s) (els : s)
| Loop (body : s)
| Break (n : nat)
| Output (e : exp)
| Seq (s1 : s) (s2 : s)
| Checkpoint (ls : list pexp).

Definition addr := nat.

Inductive env :=
| Top (f : list addr)
| Frame (f : list addr) (rst : env).

Definition extend_frame fr v :=
  match fr with
  | Top l => Top (v :: l)
  | Frame l E => Frame (v :: l) E
  end.

Fixpoint lookup_frame (e : env) n : option (list addr) :=
  match n, e with
  | 0, Top f | 0, Frame f _ => Some f
  | S n, Frame _ rst => lookup_frame rst n
  | S _, Top _ => None
  end.

Definition lookup_env (e : env) (v : var) : option addr :=
  let '(i, j) := v in
  f <- lookup_frame e i ;;
  nth_error f j.

Inductive val :=
| vInt (i : Z)
| vBool (b : bool)
| vPtr (p : addr).

Definition store := list val.

Inductive kont :=
| kMt
| kEndIf (k : kont)
| kSeq (s2 : s) (k : kont)
| kLoop (body : s) (k : kont).

Definition update_rev_nth {A} (l : list A) n v := rev (firstn n (rev l) ++ [v] ++ skipn (S n) (rev l)).
Definition rev_nth_error {A} (l : list A) n := nth_error (rev l) n.

Fixpoint eval_pexp E St p : option addr :=
  match p with
  | Var x => lookup_env E x
  | Deref p =>
    l <- eval_pexp E St p ;;
    v <- rev_nth_error St l ;;
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
  | _, _, _ => None
  end.

Fixpoint eval (E : env) (St : store) (e : exp) : option val :=
  match e with
  | Int i => ret (vInt i)
  | Bool b => ret (vBool b)
  | Ref p =>
    ptr <- eval_pexp E St p ;;
    ret (vPtr ptr)
  | Load p =>
    ptr <- eval_pexp E St p ;;
    rev_nth_error St ptr
  | Op1 o e =>
    v <- eval E St e ;;
    eval_op1 o v
  | Op2 o e1 e2 =>
    v1 <- eval E St e1 ;;
    v2 <- eval E St e2 ;;
    eval_op2 o v1 v2
  end.

Fixpoint do_break n k m : option (kont * nat) :=
  match k with
  | kEndIf k => do_break n k (S m)
  | kSeq _ k => do_break n k (S m)
  | kLoop _ k =>
    match n with
    | 0 => ret (k, m)
    | S n => do_break n k (S m)
    end
  | kMt => None
  end.

Definition CESK : Type := s * env * store * kont.
Definition checkpoint : Type := env * kont * list (addr * val).

Variant event :=
| ePure (st : CESK)
| eInput (f : val -> CESK)
| eOutput (o : val) (st : CESK)
| eCheckpoint (chkp : checkpoint) (st : CESK).


Definition next (st : CESK) : option event :=
  let '(s, E, St, k) := st in
  match s return option event with
  | Let e body =>
    v <- eval E St e ;;
    ret (ePure (body, extend_frame E (List.length St), St ++ [v], k))
  | LetInput body =>
    ret (eInput (fun v => (body, extend_frame E (List.length St), St ++ [v], k)))
  | Assign l e =>
    v <- eval E St e ;;
    ptr <- eval_pexp E St l ;;
    Some (ePure (Noop, E, update_rev_nth St ptr v, k))
  | If e s1 s2 =>
    v <- eval E St e ;;
    match v with
    | vBool b => ret (ePure (if b then s1 else s2, E, St, kEndIf k))
    | _ => None
    end
  | Loop s => ret (ePure (s, Frame [] E, St, kLoop s k))
  | Break n =>
    '(k', m) <- do_break n k 0 ;;
    (* TODO: deallocate frames broken out of *)
    ret (ePure (Noop, E, St, k'))
  | Seq s1 s2 => ret (ePure (s1, Frame [] E, St, kSeq s2 k))

  | Noop =>
    match k, E with
    | kEndIf k', Frame _ E' => ret (ePure (Noop, E', St, k'))
    | kSeq s2 k', Frame _ E' => ret (ePure (s2, E', St, k'))
    | kLoop s' k', Frame _ E' => ret (ePure (s', Frame [] E', St, kLoop s' k'))
    | kMt, _ => None
    | _, Top _ => None
    end

  | Output e =>
    v <- eval E St e ;;
    ret (eOutput v (Noop, E, St, k))

  | Checkpoint ps =>
    ls <- mapT (eval_pexp E St) ps ;;
    vs <- mapT (rev_nth_error St) ls ;;
    ret (eCheckpoint (E, k, combine ls vs) (Noop, E, St, k))
  end.

Definition do_reset (st : CESK) (p : checkpoint) : CESK :=
  let '(_, _, St, _) := st in
  let '(E, k, vs) := p in
  (Noop, E, St, k).

(* IO log, allows for nondeterminism w/ still reasoning about what inputs were seen/are the same *)

Variant io_event :=
| io_in (v : val)
| io_out (v : val)
| io_check
| io_reset.

Definition io_log := list io_event.

Definition state : Type := CESK * checkpoint * io_log.

Inductive step : state -> state -> Prop :=
| step_pure : forall c1 c2 p io,
  next c1 = Some (ePure c2) ->
  step (c1, p, io) (c2, p, io)
| step_input : forall c1 f v p io,
  next c1 = Some (eInput f) ->
  step (c1, p, io) (f v, p, io_in v :: io)
| step_output : forall c1 c2 v p io,
  next c1 = Some (eOutput v c2) ->
  step (c1, p, io) (c2, p, io_out v :: io)
| step_check : forall c1 c2 p p' io,
  next c1 = Some (eCheckpoint p c2) ->
  step (c1, p', io) (c2, p, io_check :: io)
| step_reset : forall c1 p io,
  step (c1, p, io) (do_reset c1 p, p, io_reset :: io).

(*
Inductive step : CESKP -> CESKP -> Prop :=
| step_Seq1 : forall s1 s2 E St k p, step (Seq s1 s2, E, St, k, p) (s1, E, St, kSeq s2 E k, p)
| step_Seq2 : forall s2 E E' St k p, step (Noop, E', St, kSeq s2 E k, p) (s2, E, St, k, p)

| step_Loop1 : forall s E St k p, step (Loop s, E, St, k, p) (s, E, St, kLoop s E k, p)
| step_Loop2 : forall s E E' St k p, step (Noop, E', St, kLoop s E k, p) (s, E, St, kLoop s E k, p)

| step_Break0 : forall s E E' St k p, step (Break 0, E, St, kLoop s E' k, p) (Noop, E, St, k, p)
| step_BreakS : forall n body E E' St k p,
  step (Break (S n), E, St, kLoop body E k, p) (Break n, E', St, k, p)
| step_BreakSeq : forall n E E' St s2 k p, step (Break n, E, St, kSeq s2 E' k, p) (Break n, E, St, k, p).
*)
