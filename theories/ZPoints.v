(* COQ-HEAD *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Local Open Scope Z.
(* /COQ-HEAD *)

Record point: Type := {
  x: Z;
  y: Z;
}.

Notation "p '.(x)'" := (x p) (at level 1).
Notation "p '.(y)'" := (y p) (at level 1).

Axiom point_extensionality : forall (p q : point),
  p.(x) = q.(x) /\ p.(y) = q.(y) <-> p = q.

Lemma point_dec : forall (p q : point),
  {p = q} + {~ p = q}.
Proof.
  intros.
  pose proof point_extensionality p q.
  pose proof (Z_dec p.(x) q.(x)) as [[ltx | eqx] | gtx];
  pose proof (Z_dec p.(y) q.(y)) as [[lty | eqy] | gty];
  try (right; intros H'; apply H in H' as [H1 H2]; nia).
  try (left; apply H; auto).
Qed.

Definition det (p q r : point) : Z :=
  (p.(x) * q.(y)) - (q.(x) * p.(y)) - (p.(x) * r.(y)) +
  (r.(x) * p.(y)) + (q.(x) * r.(y)) - (r.(x) * q.(y)).

Definition ccw (p q r : point) : Prop := (det p q r < 0).
Definition colinear (p q r : point) : Prop := (det p q r = 0).

Lemma ccw_dec : forall (p q r : point),
  {ccw p q r} + {~ ccw p q r}.
Proof.
  unfold ccw; intros.
  remember (det p q r) as a.
  pose proof Ztrichotomy_inf a 0 as [[H | H] | H];
  try (left; nia);
  try (right; nia).
Qed.

Lemma ccw_cyclicity : forall (p q r : point),
  ccw p q r -> ccw q r p.
Proof.
  unfold ccw, det; intros. nia. Qed.

Lemma ccw_anti_symmetry : forall (p q r : point),
  ccw p q r -> ~ ccw p r q.
Proof.
  unfold ccw, det; intros. nia. Qed.

Lemma ccw_non_degeneracy : forall (p q r : point),
  ~ colinear p q r -> ccw p q r \/ ccw p r q.
Proof.
  unfold ccw, colinear, det; intros. nia. Qed.

Lemma ccw_interiority : forall (p q r t : point),
  ccw t q r -> ccw p t r -> ccw p q t -> ccw p q r.
Proof.
  unfold ccw, det; intros. nia. Qed.

Lemma ccw_transitivity : forall (p q r s t : point),
  ccw t s p -> ccw t s q -> ccw t s r -> ccw t p q -> ccw t q r ->
  ccw t p r.
Proof.
  unfold ccw, det; intros. nia. Qed.

Lemma ccw_dual_transitivity : forall (p q r s t : point),
  ccw s t p -> ccw s t q -> ccw s t r -> ccw t p q -> ccw t q r ->
  ccw t p r.
Proof.
  unfold ccw, det; intros. nia. Qed.

Lemma ccw_trichotomy : forall (p q r : point),
  {ccw p q r} + {colinear p q r} + {ccw p r q}.
Proof.
  intros.
  destruct (ccw_dec p q r) as [H0 | H0].
  - left. left. assumption.
  - assert ({colinear p q r} + {~ colinear p q r}) as [Hcol | Hncol].
    { unfold colinear. remember (det p q r) as a.
      pose proof Z_dec a 0 as [[Hlt | Heq] | Hgt];
      try (left; assumption); 
      try (right; intros H'; nia). }
    + left. right. assumption.
    + right. pose proof (ccw_non_degeneracy p q r Hncol).
      destruct H; try contradiction; try assumption.
Qed.