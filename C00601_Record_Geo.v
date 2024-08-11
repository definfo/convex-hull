(* COQ-HEAD *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Local Open Scope Z.
(* /COQ-HEAD *)

Goal forall x1 x2 y1 y2 z: Z,
  x1 * x1 - x2 * y1 = 0 ->
  x1 * x1 * x1 = x2 * y1 * x1.
Proof.
  intros.
Abort.
Goal forall x y z: Z,
  x * x = y * z + 1 ->
  (y * z + 1) * (y + x * x) =
  x * x * (x * x + y).
Proof.
  intros.
  rewrite H.
  nia.
Qed.

Record vec: Type := {
  x: Z;
  y: Z;
}.

Notation "v '.(x)'" := (x v) (at level 1).
Notation "v '.(y)'" := (y v) (at level 1).

Definition cross_prod (v1 v2: vec): Z :=
  v1.(x) * v2.(y) - v2.(x) * v1.(y).

Definition dot_prod (v1 v2: vec): Z :=
  v1.(x) * v2.(x) + v1.(y) * v2.(y).

Definition left_equal (v1 v2: vec): Prop :=
  cross_prod v1 v2 <= 0.

Definition left_than (v1 v2: vec): Prop :=
  cross_prod v1 v2 < 0.

Definition nonzero (v: vec): Prop :=
  dot_prod v v <> 0.

Definition perp (v1 v2: vec): Prop :=
  dot_prod v1 v2 = 0.

Definition parallel (v1 v2: vec): Prop :=
  cross_prod v1 v2 = 0.

Definition forward_dir (v1 v2: vec): Prop :=
  dot_prod v1 v2 > 0.

Lemma cross_prod_comm: forall v1 v2,
  cross_prod v1 v2 = - cross_prod v2 v1.
Proof.
  unfold cross_prod.
  intros.
  lia.
Qed.

Lemma metric_nonneg: forall v,
  dot_prod v v >= 0.
Proof.
  unfold dot_prod.
  intros.
  nia.
Qed.

Lemma parallel_refl: forall v,
  parallel v v.
Proof.
  unfold parallel, cross_prod.
  intros.
  lia.
Qed.

Lemma parallel_sym: forall v1 v2,
  parallel v1 v2 ->
  parallel v2 v1.
Proof.
  unfold parallel, cross_prod.
  intros.
  lia.
Qed.

Lemma parallel_trans: forall v1 v2 v3,
  parallel v1 v2 ->
  parallel v2 v3 ->
  nonzero v2 ->
  parallel v1 v3.
Proof.
  unfold parallel, nonzero, cross_prod, dot_prod.
  intros.
  assert ((v1.(x) * v2.(y) - v2.(x) * v1.(y)) * v3.(y) = 0).
  { rewrite H. lia. }
  assert ((v1.(x) * v2.(y) - v2.(x) * v1.(y)) * v3.(x) = 0).
  { rewrite H. lia. }
  assert ((v2.(x) * v3.(y) - v3.(x) * v2.(y)) * v1.(y) = 0).
  { rewrite H0. lia. }
  assert ((v2.(x) * v3.(y) - v3.(x) * v2.(y)) * v1.(x) = 0).
  { rewrite H0. lia. }
  assert ((v1.(x) * v3.(y) - v3.(x) * v1.(y)) * v2.(x) = 0).
  { nia. }
  assert ((v1.(x) * v3.(y) - v3.(x) * v1.(y)) * v2.(y) = 0).
  { nia. }
  assert ((v1.(x) * v3.(y) - v3.(x) * v1.(y)) * v2.(x) * v2.(x) = 0).
  { rewrite H6. lia. }
  assert ((v1.(x) * v3.(y) - v3.(x) * v1.(y)) * v2.(y) * v2.(y) = 0).
  { rewrite H7. lia. }
  nia.
Qed.

Lemma perp_perp: forall v v1 v2,
  perp v v1 ->
  perp v v2 ->
  nonzero v ->
  parallel v1 v2.
Proof.
  unfold perp, nonzero, parallel, cross_prod, dot_prod.
  intros.
  assert ((v.(x) * v1.(x) + v.(y) * v1.(y)) * v2.(y) = 0).
  { rewrite H. lia. }
  assert ((v.(x) * v1.(x) + v.(y) * v1.(y)) * v2.(x) = 0).
  { rewrite H. lia. }
  assert ((v.(x) * v2.(x) + v.(y) * v2.(y)) * v1.(y) = 0).
  { rewrite H0. lia. }
  assert ((v.(x) * v2.(x) + v.(y) * v2.(y)) * v1.(x) = 0).
  { rewrite H0. lia. }
  assert ((v1.(x) * v2.(y) - v2.(x) * v1.(y)) * v.(x) = 0).
  { nia. }
  assert ((v1.(x) * v2.(y) - v2.(x) * v1.(y)) * v.(y) = 0).
  { nia. }
  assert ((v1.(x) * v2.(y) - v2.(x) * v1.(y)) * v.(x) * v.(x) = 0).
  { rewrite H6. lia. }
  assert ((v1.(x) * v2.(y) - v2.(x) * v1.(y)) * v.(y) * v.(y) = 0).
  { rewrite H7. lia. }
  nia.
Qed.

Lemma nonneg_le_trans: forall v1 v2 v3: vec,
  v1.(y) > 0 ->
  v2.(y) > 0 ->
  v3.(y) >= 0 ->
  left_equal v1 v2 ->
  left_equal v2 v3 ->
  left_equal v1 v3.
Proof.
  unfold left_equal, cross_prod.
  intros.
  assert (v1.(x) * v2.(y) * v3.(y) - v2.(x) * v1.(y) * v3.(y) <= 0).
  { nia. }
  assert (v2.(x) * v3.(y) * v1.(y) - v3.(x) * v2.(y) * v1.(y) <= 0).
  { nia. }
  assert (v1.(x) * v3.(y) * v2.(y) - v3.(x) * v1.(y) * v2.(y) <= 0).
  { nia. }
  nia.
Qed.

Lemma le_trans: forall v v1 v2 v3: vec,
  left_than v1 v ->
  left_than v2 v ->
  left_equal v3 v ->
  left_equal v1 v2 ->
  left_equal v2 v3 ->
  left_equal v1 v3.
Proof.
  unfold left_equal, left_than, cross_prod.
  intros.
  nia.
Qed.

Lemma forward_left: forall v v1 v2: vec,
  forward_dir v v1 ->
  forward_dir v v2 ->
  left_than v1 v ->
  left_than v2 v ->
  forward_dir v1 v2.
Proof.
  unfold left_than, forward_dir, cross_prod, dot_prod.
  intros.
  nia.
Qed.

Definition left_45deg (v1 v2: vec): Prop :=
  cross_prod v1 v2 + dot_prod v1 v2 = 0.

Lemma double_left_45deg: forall v1 v2 v3,
  left_45deg v1 v2 ->
  left_45deg v2 v3 ->
  nonzero v2 ->
  perp v1 v3.
Proof.
  unfold left_45deg, nonzero, perp, dot_prod, cross_prod.
  intros.
  assert ((v1.(x) * v2.(y) - v2.(x) * v1.(y) + (v1.(x) * v2.(x) + v1.(y) * v2.(y))) * (v3.(x) + v3.(y)) = 0).
  { rewrite H. lia. }
  assert ((v1.(x) * v2.(y) - v2.(x) * v1.(y) + (v1.(x) * v2.(x) + v1.(y) * v2.(y))) * (v3.(x) - v3.(y)) = 0).
  { rewrite H. lia. }
  assert ((v2.(x) * v3.(y) - v3.(x) * v2.(y) + (v2.(x) * v3.(x) + v2.(y) * v3.(y))) * (v1.(x) + v1.(y)) = 0).
  { rewrite H0. lia. }
  assert ((v2.(x) * v3.(y) - v3.(x) * v2.(y) + (v2.(x) * v3.(x) + v2.(y) * v3.(y))) * (v1.(x) - v1.(y)) = 0).
  { rewrite H0. lia. }
  assert ((v1.(x) * v3.(x) + v1.(y) * v3.(y)) * v2.(y) = 0).
  { nia. }
  assert ((v1.(x) * v3.(x) + v1.(y) * v3.(y)) * v2.(x) = 0).
  { nia. }
  assert ((v1.(x) * v3.(x) + v1.(y) * v3.(y)) * v2.(y) * v2.(y) = 0).
  { rewrite H6. lia. }
  assert ((v1.(x) * v3.(x) + v1.(y) * v3.(y)) * v2.(x) * v2.(x) = 0).
  { rewrite H7. lia. }
  nia.
Qed.

Lemma less_than_nonzero1: forall v1 v2,
  left_than v1 v2 ->
  nonzero v1.
Proof.
  unfold nonzero, left_than, cross_prod, dot_prod.
  intros.
  assert ((v1.(x) * v2.(y) - v2.(x) * v1.(y)) * (v1.(x) * v2.(y) - v2.(x) * v1.(y)) > 0).
  { nia. }
  assert (forall x, x * x >= 0). { intros. nia. }
  specialize (H1 (v1.(x) * v2.(x) + v1.(y) * v2.(y))).
  assert ((v1.(x) * v1.(x) + v1.(y) * v1.(y)) * (v2.(x) * v2.(x) + v2.(y) * v2.(y)) > 0).
  { nia. }
  nia.
Qed.

Lemma left_than_same_dir_l: forall v1 v2 v,
  parallel v1 v2 ->
  forward_dir v1 v2 ->
  left_equal v1 v ->
  left_equal v2 v.
Proof.
  unfold parallel, forward_dir, left_than, left_equal, cross_prod, dot_prod.
  intros.
  assert ((v1.(x) * v.(y) - v.(x) * v1.(y)) * v2.(y) * v2.(y) <= 0).
  { nia. }
  assert ((v1.(x) * v2.(y) - v2.(x) * v1.(y)) * v.(y) * v2.(y) = 0).
  { rewrite H. lia. }
  assert ((v2.(x) * v.(y) - v.(x) * v2.(y)) * (v1.(y) * v2.(y)) <= 0).
  { nia. }
  assert ((v1.(x) * v.(y) - v.(x) * v1.(y)) * v2.(x) * v2.(x) <= 0).
  { nia. }
  assert ((v1.(x) * v2.(y) - v2.(x) * v1.(y)) * v.(x) * v2.(x) = 0).
  { rewrite H. lia. }
  assert ((v2.(x) * v.(y) - v.(x) * v2.(y)) * (v1.(x) * v2.(x)) <= 0).
  { nia. }
  assert ((v2.(x) * v.(y) - v.(x) * v2.(y)) * (v1.(x) * v2.(x) + v1.(y) * v2.(y)) <= 0).
  { nia. }
  nia.
Qed.

Lemma left_than_same_dir_r: forall v1 v2 v,
  parallel v1 v2 ->
  forward_dir v1 v2 ->
  left_equal v v1 ->
  left_equal v v2.
Proof.
  unfold parallel, forward_dir, left_than, left_equal, cross_prod, dot_prod.
  intros.
  assert ((v.(x) * v1.(y) - v1.(x) * v.(y)) * v2.(y) * v2.(y) <= 0).
  { nia. }
  assert ((v1.(x) * v2.(y) - v2.(x) * v1.(y)) * v.(y) * v2.(y) = 0).
  { rewrite H. lia. }
  assert ((v.(x) * v2.(y) - v2.(x) * v.(y)) * (v1.(y) * v2.(y)) <= 0).
  { nia. }
  assert ((v.(x) * v1.(y) - v1.(x) * v.(y)) * v2.(x) * v2.(x) <= 0).
  { nia. }
  assert ((v1.(x) * v2.(y) - v2.(x) * v1.(y)) * v.(x) * v2.(x) = 0).
  { rewrite H. lia. }
  assert ((v.(x) * v2.(y) - v2.(x) * v.(y)) * (v1.(x) * v2.(x)) <= 0).
  { nia. }
  assert ((v.(x) * v2.(y) - v2.(x) * v.(y)) * (v1.(x) * v2.(x) + v1.(y) * v2.(y)) <= 0).
  { nia. }
  nia.
Qed.
