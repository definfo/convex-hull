Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
From ConvexHull Require Import Record_Geo_Point Record_Geo_Vec.

Local Open Scope Z_scope.

(** Compatibility layer for point-level geometric predicates.

    [Record_Geo_Point] is the canonical home for these predicates. This file
    keeps the earlier [ConvexHull.Geo_Predicates.*] names without maintaining
    duplicate definitions. *)

Definition colinear : point -> point -> point -> Prop :=
  Record_Geo_Point.colinear.

Definition at_mid : point -> point -> point -> Prop :=
  Record_Geo_Point.at_mid.

Lemma colinear_comm : forall p q r,
  colinear p q r <-> colinear p r q.
Proof.
  apply Record_Geo_Point.colinear_comm.
Qed.

Lemma at_mid_comm : forall p q r,
  at_mid p q r <-> at_mid p r q.
Proof.
  apply Record_Geo_Point.at_mid_comm.
Qed.

Definition left_than (u v : vec) : Prop :=
  cross_prod u v > 0.

Definition ccw : point -> point -> point -> Prop :=
  Record_Geo_Point.ccw.

Lemma ccw_iff_cross_pos : forall a b c,
  ccw a b c <-> cross_prod (build_vec a b) (build_vec a c) > 0.
Proof.
  intros a b c.
  unfold ccw, Record_Geo_Point.ccw, Record_Geo_Vec.left_than.
  rewrite cross_prod_comm.
  split; lia.
Qed.

Definition ccw_dec (a b c : point) : {ccw a b c} + {~ ccw a b c} :=
  Record_Geo_Point.ccw_dec a b c.
