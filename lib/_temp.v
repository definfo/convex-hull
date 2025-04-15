Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
From ConvexHull Require Import Record_Geo_Vec Record_Geo_Point.
Local Open Scope Z.

Lemma Z_ge_dec : forall (a b : Z),
  a >= b -> {a > b} + {a = b}.
Proof.
  intros.
  apply Z.ge_le in H.
  apply Z_le_lt_eq_dec in H.
  destruct H.
  - left; nia.
  - right. lia.
Qed.

Lemma dot_prod_zero_dec : forall a b,
  dot_prod (build_vec a b) (build_vec a b) = 0 ->
  a = b.
Proof.
  unfold dot_prod; simpl; intros.
  destruct a, b; simpl in H.
  remember (point_x0 - point_x) as x;
  remember (point_y0 - point_y) as y.
  assert (x = 0 /\ y = 0). { nia. }
  assert (point_x0 = point_x /\ point_y0 = point_y). { lia. }
  destruct H1; subst. tauto.
Qed.

Lemma dot_prod_sqr_dec : forall a b,
  dot_prod (build_vec a b) (build_vec a b) >= 0 ->
  {a = b} + {dot_prod (build_vec a b) (build_vec a b) > 0}.
Proof.
  intros; remember (dot_prod (build_vec a b) (build_vec a b)).
  apply Z_ge_dec in H; destruct H.
  - right; tauto. 
  - left; apply dot_prod_zero_dec; lia.
Qed.


Search (_ >= 0) in Z.
