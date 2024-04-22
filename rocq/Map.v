From Coq Require Import Equalities.

Set Implicit Arguments.

Module EMap (D : DecidableType).

  Definition key := D.t.
  Definition key_eq := D.eq_dec.

  Section Elt.
  Variable elt : Type.
  Definition t := key -> elt.
  Definition init (v : elt) := fun (_ : key) => v.
  Definition get (x : key) (m : t) := m x.
  Definition set (x : key) (v : elt) (m : t) : t :=
    fun (y : key) => if key_eq y x then v else m y.

  Lemma get_init : forall (x : key) (v : elt), get x (init v) = v.
  Proof. intros. reflexivity. Qed.

  Lemma get_set_eq : forall (x : key) (v : elt) (m : t),
    get x (set x v m) = v.
  Proof.
    intros.
    unfold get, set.
    case (key_eq x x); intros.
    - reflexivity.
    - destruct n. apply D.eq_equiv.
  Qed.

  Lemma get_set_neq : forall (x y : key) (v : elt) (m : t),
    ~ D.eq x y -> (get x (set y v m)) = (get x m).
  Proof.
    intros.
    unfold get, set.
    case (key_eq x y); intros.
    - contradiction.
    - reflexivity.
  Qed.

  End Elt.

End EMap.