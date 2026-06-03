Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.setoid_ring.Ring.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.QCP_demos_LLM.simple_arith Require Import exgcd_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma Zabs_triangle: forall a b, Zabs(a - b) <= Zabs a + Zabs b.
Proof. lia. Qed.

Lemma Z_gcd_divide_l: forall a b, exists a', a = a' * (Zgcd a b).
Proof.
  intros.
  pose proof Z.gcd_divide_l a b.
  unfold Z.divide in H.
  exact H.
Qed.

Lemma Z_gcd_divide_r: forall a b, exists b', b = b' * (Zgcd a b).
Proof.
  intros.
  pose proof Z.gcd_divide_r a b.
  unfold Z.divide in H.
  exact H.
Qed.

Lemma Z_abs_quot_rem:
  forall a b: Z, b <> 0 -> Zabs (a % (b)) + Zabs (a ÷ b) * Zabs b = Zabs a.
Proof.
  intros.
  assert(Zabs b <> 0) by lia.
  pose proof Z.quot_rem (Zabs a) (Zabs b) H0.
  rewrite <- Z.quot_abs. 2 : lia.
  rewrite <- Z.rem_abs. 2 : lia.
  lia.
Qed.

Lemma Z_gcd_pos_l:
  forall a b, a <> 0 -> Zgcd a b > 0.
Proof.
  intros.
  assert(Zgcd a b <> 0). {
    intros. intro.
    pose proof Z.gcd_eq_0_l a b.
    lia.
  }
  pose proof Z.gcd_nonneg a b.
  lia.
Qed.

Lemma Z_gcd_pos_r:
  forall a b, b <> 0 -> Zgcd a b > 0.
Proof.
  intros.
  assert(Zgcd a b <> 0). {
    intros. intro.
    pose proof Z.gcd_eq_0_r a b.
    lia.
  }
  pose proof Z.gcd_nonneg a b.
  lia.
Qed.

(* Proof goal: 
  |x'| <= |(a % b) / g|
  |y'| <= |b / g|
  x = y'
  y = x' - (a / b) * y'
  ===> 
  |x| <= |b / g|
  |y| <= |a / g|

  informal Proof:
  |y| =  |x' - (a / b) * y'|
      <= |x'| + |a / b| * |y'|
      <= |(a % b) / g| + |a / b| * |b / g|
      =  |(|a % b| + |a / b| * |b|) / g|     (since g | (a % b) and g | b)
      =  |a / g|
*)

Lemma exgcd_reduction_pre:
  forall a b y, 
  b <> 0 ->
  Zabs y <= Zabs b ÷ Zgcd b (a % (b)) ->
  Zabs (a ÷ b * y) <= Zabs (a ÷ b) * (Zabs b ÷ Zgcd b (a % (b))).
Proof.
  intros.
  rewrite Z.abs_mul. nia.
Qed.

Lemma exgcd_reduction':
  forall a b x y, 
  b <> 0 ->
  Zabs x <= Zabs (a % (b)) ÷ Zgcd b (a % (b)) -> 
  Zabs y <= Zabs b ÷ Zgcd b (a % (b)) ->
  Zabs (x) + Zabs (a ÷ b * y) <= Zabs a ÷ Zgcd b (a % (b)).
Proof.
  intros.
  eapply Z.le_trans. 1: apply (Zplus_le_compat_r _ _ _ H0).
  pose proof exgcd_reduction_pre a b y H H1.
  eapply Z.le_trans. 1: apply (Zplus_le_compat_l _ _ _ H2).
  replace (Zabs (a % (b)) ÷ Zgcd b (a % (b)) + 
          Zabs (a ÷ b) * (Zabs b ÷ Zgcd b (a % (b)))) 
    with (Zabs(((Zabs(a % (b))) + Zabs(a ÷ b) * Zabs(b)) ÷ Zgcd b (a % (b)))).
  2: {
    replace (Zgcd b (a % (b))) with (Zgcd a b) in *.
    2: { rewrite Z.gcd_comm. rewrite <- Z.gcd_rem. rewrite Z.gcd_comm. lia. lia. }
    pose proof Z_gcd_divide_l a b as H_adiv.
    pose proof Z_gcd_divide_r a b as H_bdiv.
    destruct H_adiv as [a' H_adiv].
    destruct H_bdiv as [b' H_bdiv].
    pose proof Z_gcd_pos_r a b H.
    set (g := Zgcd a b) in *.
    replace (a % (b)) with (a' % (b') * g).
    2: { rewrite H_adiv, H_bdiv. rewrite Zquot.Zmult_rem_distr_r. reflexivity. }
    replace (a ÷ b) with (a' ÷ b').
    2: { rewrite H_adiv, H_bdiv. rewrite Zquot.Zquot_mult_cancel_r; lia. }
    replace (Zabs (a' ÷ b') * (Zabs b ÷ g)) with (Zabs (a' ÷ b') * Zabs b ÷ g).
    2: { rewrite Z.divide_quot_mul_exact; try lia. 
        unfold Z.divide.
        exists (Z.abs b').
        rewrite H_bdiv.
        replace g with (Zabs g) at 2 by lia.
        apply Z.abs_mul. }
    replace (Zabs ((Zabs (a' % (b') * g) + Zabs (a' ÷ b') * Zabs b) ÷ g)) 
      with ((Zabs (a' % (b') * g) + Zabs (a' ÷ b') * Zabs b) ÷ g).
    2: {
      pose proof Z.abs_eq_iff ((Zabs (a' % (b') * g) + Zabs (a' ÷ b') * Zabs b) ÷ g) as H_abspos.
      rewrite (proj2 H_abspos). 1 : reflexivity.
      assert((Zabs (a' % (b') * g) + Zabs (a' ÷ b') * Zabs b) >= 0) by lia.
      apply Z.quot_pos; lia.
    }
    replace (Zabs b) with (Zabs b' * g) by lia.
    rewrite Z.mul_assoc.
    rewrite Zquot.Z_quot_plus.
    + rewrite Z.quot_mul; lia.
    + lia.
    + lia. 
  }
  pose proof Z_gcd_pos_l b (a % (b)) H.
  rewrite <- Z.quot_abs by ltac:(lia).
  rewrite Z_abs_quot_rem by ltac:(lia).
  rewrite Z.abs_idemp.
  replace (Zabs (Zgcd b (a % (b)))) with (Zgcd b (a % (b))) by lia.
  lia.
Qed.

Lemma exgcd_reduction:
  forall a b x y, 
  b <> 0 ->
  Zabs x <= Zabs (a % (b)) ÷ Zgcd b (a % (b)) -> 
  Zabs y <= Zabs b ÷ Zgcd b (a % (b)) ->
  Zabs (x - a ÷ b * y) <= Zabs a ÷ Zgcd b (a % (b)).
Proof.
  intros.
  eapply Z.le_trans. 1: apply Zabs_triangle.
  apply (exgcd_reduction' _ _ _ _ H H0 H1).
Qed.

Lemma proof_of_exgcd_return_wit_3 : exgcd_return_wit_3.
Proof.
  pre_process.
  pose proof Z.gcd_rem a_pre b_pre H4 as Hgcd.
  rewrite H1 in Hgcd.
  rewrite Z.gcd_0_l in Hgcd.
  rewrite Z.gcd_comm in Hgcd.
  Left.
  Right.
  Exists x_callee_v.
  Exists 0.
  split_pure_spatial.
  - rewrite H3.
    replace (x_callee_v - a_pre ÷ b_pre * 0) with x_callee_v by lia.
    cancel.
  - split_pures.
    + dump_pre_spatial.
      rewrite H1 in H.
      rewrite Z.gcd_0_r in H.
      rewrite H.
      exact Hgcd.
    + dump_pre_spatial.
      rewrite H3, H1 in H0.
      rewrite Z.gcd_0_r in H0.
      rewrite <- Hgcd.
      lia.
    + dump_pre_spatial. exact H4.
    + dump_pre_spatial. exact H1.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. exact H2.
Qed.

Lemma proof_of_exgcd_return_wit_2 : exgcd_return_wit_2.
Proof.
  pre_process.
  assert (Hgcd1 : Zgcd b_pre (a_pre % (b_pre)) = Zgcd a_pre b_pre).
  {
    rewrite Z.gcd_comm.
    rewrite (Z.gcd_comm a_pre b_pre).
    apply Z.gcd_rem.
    exact H5.
  }
  assert (Hy_bound :
    Zabs y_callee_v <= Zabs b_pre ÷ Zgcd b_pre (a_pre % (b_pre))).
  {
    assert (Hgcd2 : Zgcd b_pre (a_pre % (b_pre)) = Zabs (a_pre % (b_pre))).
    {
      pose proof Z.gcd_rem b_pre (a_pre % (b_pre)) H1 as Htmp.
      rewrite H2 in Htmp.
      rewrite Z.gcd_0_l in Htmp.
      rewrite Z.gcd_comm.
      exact (eq_sym Htmp).
    }
    pose proof Z_gcd_divide_l b_pre (a_pre % (b_pre)) as Hdiv.
    destruct Hdiv as [k Hk].
    assert (Hk_nonzero : k <> 0).
    {
      intro Hk0.
      rewrite Hk0 in Hk.
      apply H5.
      lia.
    }
    assert (Hq_ge_1 : 1 <= Zabs b_pre ÷ Zgcd b_pre (a_pre % (b_pre))).
    {
      assert (Hquotk : Zabs b_pre ÷ Zgcd b_pre (a_pre % (b_pre)) = Zabs k).
      {
        rewrite Hgcd2.
        assert (Habsb : Zabs b_pre = Zabs (k * Zgcd b_pre (a_pre % (b_pre)))).
        {
          replace b_pre with (k * Zgcd b_pre (a_pre % (b_pre))) at 1 by exact (eq_sym Hk).
          reflexivity.
        }
        rewrite Habsb.
        rewrite Z.abs_mul.
        replace (Zabs (Zgcd b_pre (a_pre % (b_pre)))) with (Zgcd b_pre (a_pre % (b_pre))) by lia.
        rewrite Hgcd2.
        replace
          ((Zabs k * Zabs (a_pre % (b_pre))) ÷ Zabs (a_pre % (b_pre)))
          with (Zabs k).
        - reflexivity.
        - rewrite Z.quot_mul.
          + reflexivity.
          + assert (Zabs (a_pre % (b_pre)) <> 0) by lia.
            exact H10.
      }
      rewrite Hquotk.
      assert (1 <= Zabs k) by lia.
      lia.
    }
    lia.
  }
  assert (Hbound :
    Zabs (0 - a_pre ÷ b_pre * y_callee_v) <=
    Zabs a_pre ÷ Zgcd a_pre b_pre).
  {
    pose proof (exgcd_reduction a_pre b_pre 0 y_callee_v H5) as Htmp.
    assert (0 <= Zabs (a_pre % (b_pre)) ÷ Zgcd b_pre (a_pre % (b_pre))).
    {
      apply Z.quot_pos.
      - pose proof Z.abs_nonneg (a_pre % (b_pre)).
        lia.
      - pose proof (Z_gcd_pos_r b_pre (a_pre % (b_pre)) H1).
        lia.
    }
    assert (Zabs 0 <= Zabs (a_pre % (b_pre)) ÷ Zgcd b_pre (a_pre % (b_pre))) by lia.
    specialize (Htmp H11 Hy_bound).
    rewrite Hgcd1 in Htmp.
    exact Htmp.
  }
  pose proof Z.quot_rem a_pre b_pre H5 as Hqr.
  Right.
  Exists (x_callee_v - a_pre ÷ b_pre * y_callee_v).
  Exists y_callee_v.
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial. rewrite H. exact Hgcd1.
    + dump_pre_spatial.
      rewrite <- Hgcd1.
      assert (Heq:
        a_pre * y_callee_v + b_pre * (x_callee_v - a_pre ÷ b_pre * y_callee_v) =
        b_pre * x_callee_v + a_pre % (b_pre) * y_callee_v).
      {
        assert (Haqy:
          a_pre * y_callee_v =
          (b_pre * (a_pre ÷ b_pre) + a_pre % (b_pre)) * y_callee_v).
        {
          replace a_pre with (b_pre * (a_pre ÷ b_pre) + a_pre % (b_pre)) at 1 by exact (eq_sym Hqr).
          reflexivity.
        }
        rewrite Haqy.
        replace
          ((b_pre * (a_pre ÷ b_pre) + a_pre % (b_pre)) * y_callee_v)
          with (b_pre * (a_pre ÷ b_pre) * y_callee_v + a_pre % (b_pre) * y_callee_v)
          by nia.
        replace
          (b_pre * (x_callee_v - a_pre ÷ b_pre * y_callee_v))
          with (b_pre * x_callee_v - b_pre * (a_pre ÷ b_pre) * y_callee_v)
          by nia.
        replace
          (b_pre * (a_pre ÷ b_pre) * y_callee_v + a_pre % (b_pre) * y_callee_v +
           (b_pre * x_callee_v - b_pre * (a_pre ÷ b_pre) * y_callee_v))
          with
          ((b_pre * (a_pre ÷ b_pre) * y_callee_v -
            b_pre * (a_pre ÷ b_pre) * y_callee_v) +
           (a_pre % (b_pre) * y_callee_v + b_pre * x_callee_v))
          by nia.
        replace
          (b_pre * (a_pre ÷ b_pre) * y_callee_v -
           b_pre * (a_pre ÷ b_pre) * y_callee_v) with 0 by nia.
        replace (a_pre % (b_pre) * y_callee_v + b_pre * x_callee_v)
          with (b_pre * x_callee_v + a_pre % (b_pre) * y_callee_v) by nia.
        replace (0 + (b_pre * x_callee_v + a_pre % (b_pre) * y_callee_v))
          with (b_pre * x_callee_v + a_pre % (b_pre) * y_callee_v) by nia.
        reflexivity.
      }
      rewrite Heq.
      rewrite H3.
      rewrite H3 in H0.
      exact H0.
    + dump_pre_spatial. exact H5.
    + dump_pre_spatial. exact H1.
    + dump_pre_spatial. rewrite <- Hgcd1. exact Hy_bound.
    + dump_pre_spatial. rewrite H3. exact Hbound.
Qed.

Lemma proof_of_exgcd_return_wit_1 : exgcd_return_wit_1.
Proof.
  pre_process.
  assert (Hgcd : Zgcd b_pre (a_pre % (b_pre)) = Zgcd a_pre b_pre).
  {
    rewrite Z.gcd_comm.
    rewrite (Z.gcd_comm a_pre b_pre).
    apply Z.gcd_rem.
    exact H5.
  }
  pose proof Z.quot_rem a_pre b_pre H5 as Hqr.
  pose proof (exgcd_reduction a_pre b_pre x_callee_v y_callee_v H5 H3 H4) as Hbound.
  rewrite Hgcd in Hbound.
  Right.
  Exists (x_callee_v - a_pre ÷ b_pre * y_callee_v).
  Exists y_callee_v.
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial. rewrite H. exact Hgcd.
    + dump_pre_spatial.
      rewrite <- Hgcd.
      assert (Heq:
        a_pre * y_callee_v + b_pre * (x_callee_v - a_pre ÷ b_pre * y_callee_v) =
        b_pre * x_callee_v + a_pre % (b_pre) * y_callee_v).
      {
        assert (Haqy:
          a_pre * y_callee_v =
          (b_pre * (a_pre ÷ b_pre) + a_pre % (b_pre)) * y_callee_v).
        {
          replace a_pre with (b_pre * (a_pre ÷ b_pre) + a_pre % (b_pre)) at 1 by exact (eq_sym Hqr).
          reflexivity.
        }
        rewrite Haqy.
        replace
          ((b_pre * (a_pre ÷ b_pre) + a_pre % (b_pre)) * y_callee_v)
          with (b_pre * (a_pre ÷ b_pre) * y_callee_v + a_pre % (b_pre) * y_callee_v)
          by nia.
        replace
          (b_pre * (x_callee_v - a_pre ÷ b_pre * y_callee_v))
          with (b_pre * x_callee_v - b_pre * (a_pre ÷ b_pre) * y_callee_v)
          by nia.
        replace
          (b_pre * (a_pre ÷ b_pre) * y_callee_v + a_pre % (b_pre) * y_callee_v +
           (b_pre * x_callee_v - b_pre * (a_pre ÷ b_pre) * y_callee_v))
          with
          ((b_pre * (a_pre ÷ b_pre) * y_callee_v -
            b_pre * (a_pre ÷ b_pre) * y_callee_v) +
           (a_pre % (b_pre) * y_callee_v + b_pre * x_callee_v))
          by nia.
        replace
          (b_pre * (a_pre ÷ b_pre) * y_callee_v -
           b_pre * (a_pre ÷ b_pre) * y_callee_v) with 0 by nia.
        replace (a_pre % (b_pre) * y_callee_v + b_pre * x_callee_v)
          with (b_pre * x_callee_v + a_pre % (b_pre) * y_callee_v) by nia.
        replace (0 + (b_pre * x_callee_v + a_pre % (b_pre) * y_callee_v))
          with (b_pre * x_callee_v + a_pre % (b_pre) * y_callee_v) by nia.
        reflexivity.
      }
      rewrite Heq.
      exact H0.
    + dump_pre_spatial. exact H5.
    + dump_pre_spatial. exact H1.
    + dump_pre_spatial. rewrite <- Hgcd. exact H4.
    + dump_pre_spatial. exact Hbound.
Qed.

Lemma proof_of_exgcd_return_wit_4 : exgcd_return_wit_4.
Proof.
  pre_process.
  Left.
  Left.
  Exists 0.
  Exists 1.
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial. rewrite H, H2, Z.gcd_0_r. rewrite Z.abs_eq; lia.
    + dump_pre_spatial. rewrite H2, Z.gcd_0_r. rewrite Z.abs_eq; lia.
    + dump_pre_spatial. exact H2.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. reflexivity.
Qed.

Lemma proof_of_exgcd_return_wit_5 : exgcd_return_wit_5.
Proof.
  pre_process.
  Left.
  Left.
  Exists 0.
  Exists 0.
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial. rewrite H, H0, H2, Z.gcd_0_r. reflexivity.
    + dump_pre_spatial. rewrite H0, H2, Z.gcd_0_r. lia.
    + dump_pre_spatial. exact H2.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. reflexivity.
Qed.

Lemma proof_of_exgcd_return_wit_6 : exgcd_return_wit_6.
Proof.
  pre_process.
  Left.
  Left.
  Exists 0.
  Exists (-1).
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial. rewrite H, H1, Z.gcd_0_r. rewrite Z.abs_neq; lia.
    + dump_pre_spatial.
      rewrite H1, Z.gcd_0_r.
      replace (a_pre * -1 + b_pre * 0) with (- a_pre) by lia.
      rewrite Z.abs_neq; lia.
    + dump_pre_spatial. exact H1.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. reflexivity.
Qed.

Lemma proof_of_exgcd_partial_solve_wit_4_pure : exgcd_partial_solve_wit_4_pure.
Proof.
  pre_process.
  pose proof Z.rem_bound_abs a_pre b_pre H.
  split_pures.
  - dump_pre_spatial. exact H2.
  - dump_pre_spatial. exact H3.
  - dump_pre_spatial. lia.
  - dump_pre_spatial. lia.
Qed.

Lemma proof_of_exgcd_safety_wit_12 : exgcd_safety_wit_12.
Proof.
  pre_process.
  assert (Hgpos : Zgcd b_pre (a_pre % (b_pre)) > 0).
  { apply Z_gcd_pos_r. exact H1. }
  assert (Habs_bound :
    Zabs (x_callee_v - a_pre ÷ b_pre * y_callee_v) <=
    Zabs a_pre ÷ Zgcd b_pre (a_pre % (b_pre))).
  {
    apply exgcd_reduction; auto.
  }
  assert (Hquot_le : Zabs a_pre ÷ Zgcd b_pre (a_pre % (b_pre)) <= Zabs a_pre).
  {
    apply Z.quot_le_upper_bound; try lia.
    pose proof Z.abs_nonneg a_pre.
    nia.
  }
  assert (Ha_int : Zabs a_pre <= INT_MAX) by lia.
  assert (Habs_int : Zabs (x_callee_v - a_pre ÷ b_pre * y_callee_v) <= INT_MAX).
  {
    eapply Z.le_trans with (m := Zabs a_pre ÷ Zgcd b_pre (a_pre % (b_pre))).
    - exact Habs_bound.
    - eapply Z.le_trans.
      + exact Hquot_le.
      + exact Ha_int.
  }
  apply (proj1 (Z.abs_le (x_callee_v - a_pre ÷ b_pre * y_callee_v) INT_MAX)) in Habs_int.
  destruct Habs_int as [Hlo Hhi].
  split_pures.
  - dump_pre_spatial. exact Hhi.
  - dump_pre_spatial. lia.
Qed.

Lemma proof_of_exgcd_safety_wit_13 : exgcd_safety_wit_13.
Proof.
  pre_process.
  assert (Hgpos : Zgcd b_pre (a_pre % (b_pre)) > 0).
  { apply Z_gcd_pos_r. exact H1. }
  assert (Habs_bound0 :
    Zabs (0 - a_pre ÷ b_pre * y_callee_v) <=
    Zabs a_pre ÷ Zgcd b_pre (a_pre % (b_pre))).
  {
    apply exgcd_reduction with (x := 0); auto.
    lia.
  }
  assert (Habs_bound :
    Zabs (a_pre ÷ b_pre * y_callee_v) <=
    Zabs a_pre ÷ Zgcd b_pre (a_pre % (b_pre))).
  {
    replace (a_pre ÷ b_pre * y_callee_v) with (- (0 - a_pre ÷ b_pre * y_callee_v)) by lia.
    rewrite Z.abs_opp.
    exact Habs_bound0.
  }
  assert (Hquot_le : Zabs a_pre ÷ Zgcd b_pre (a_pre % (b_pre)) <= Zabs a_pre).
  {
    apply Z.quot_le_upper_bound; try lia.
    pose proof Z.abs_nonneg a_pre.
    nia.
  }
  assert (Ha_int : Zabs a_pre <= INT_MAX) by lia.
  assert (Habs_int : Zabs (a_pre ÷ b_pre * y_callee_v) <= INT_MAX).
  {
    eapply Z.le_trans with (m := Zabs a_pre ÷ Zgcd b_pre (a_pre % (b_pre))).
    - exact Habs_bound.
    - eapply Z.le_trans.
      + exact Hquot_le.
      + exact Ha_int.
  }
  apply (proj1 (Z.abs_le (a_pre ÷ b_pre * y_callee_v) INT_MAX)) in Habs_int.
  destruct Habs_int as [Hlo Hhi].
  split_pures.
  - dump_pre_spatial. exact Hhi.
  - dump_pre_spatial. lia.
Qed.

Lemma proof_of_exgcd_safety_wit_15 : exgcd_safety_wit_15.
Proof.
  pre_process.
  assert (Hbabs_pos : Zabs b_pre > 0) by lia.
  assert (Hquot_abs : Zabs (a_pre ÷ b_pre) = Zabs a_pre ÷ Zabs b_pre).
  { rewrite Z.quot_abs; lia. }
  assert (Hquot_le : Zabs (a_pre ÷ b_pre) <= Zabs a_pre).
  {
    rewrite Hquot_abs.
    apply Z.quot_le_upper_bound; try lia.
    pose proof Z.abs_nonneg a_pre.
    nia.
  }
  assert (Hmul_le : Zabs (a_pre ÷ b_pre * y_callee_v) <= Zabs (a_pre ÷ b_pre)).
  {
    rewrite Z.abs_mul.
    nia.
  }
  assert (Habs_int : Zabs (x_callee_v - a_pre ÷ b_pre * y_callee_v) <= INT_MAX).
  {
    rewrite H3.
    replace (0 - a_pre ÷ b_pre * y_callee_v) with (- (a_pre ÷ b_pre * y_callee_v)) by lia.
    rewrite Z.abs_opp.
    eapply Z.le_trans with (m := Zabs (a_pre ÷ b_pre)).
    - exact Hmul_le.
    - eapply Z.le_trans.
      + exact Hquot_le.
      + lia.
  }
  apply (proj1 (Z.abs_le (x_callee_v - a_pre ÷ b_pre * y_callee_v) INT_MAX)) in Habs_int.
  destruct Habs_int as [Hlo Hhi].
  split_pures.
  - dump_pre_spatial. exact Hhi.
  - dump_pre_spatial. lia.
Qed.

Lemma proof_of_exgcd_safety_wit_16 : exgcd_safety_wit_16.
Proof.
  pre_process.
  assert (Hbabs_pos : Zabs b_pre > 0) by lia.
  assert (Hquot_abs : Zabs (a_pre ÷ b_pre) = Zabs a_pre ÷ Zabs b_pre).
  { rewrite Z.quot_abs; lia. }
  assert (Hquot_le : Zabs (a_pre ÷ b_pre) <= Zabs a_pre).
  {
    rewrite Hquot_abs.
    apply Z.quot_le_upper_bound; try lia.
    pose proof Z.abs_nonneg a_pre.
    nia.
  }
  assert (Hmul_le : Zabs (a_pre ÷ b_pre * y_callee_v) <= Zabs (a_pre ÷ b_pre)).
  {
    rewrite Z.abs_mul.
    nia.
  }
  assert (Habs_int : Zabs (a_pre ÷ b_pre * y_callee_v) <= INT_MAX).
  {
    eapply Z.le_trans with (m := Zabs (a_pre ÷ b_pre)).
    - exact Hmul_le.
    - eapply Z.le_trans.
      + exact Hquot_le.
      + lia.
  }
  apply (proj1 (Z.abs_le (a_pre ÷ b_pre * y_callee_v) INT_MAX)) in Habs_int.
  destruct Habs_int as [Hlo Hhi].
  split_pures.
  - dump_pre_spatial. exact Hhi.
  - dump_pre_spatial. lia.
Qed.

Lemma proof_of_exgcd_safety_wit_18 : exgcd_safety_wit_18.
Proof.
  pre_process.
Qed.

Lemma proof_of_exgcd_safety_wit_19 : exgcd_safety_wit_19.
Proof.
  pre_process.
Qed.

Lemma proof_of_exgcd_derive_Inter_by_Proof: exgcd_derive_Inter_by_Proof.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel.
    apply derivable1_wand_sepcon_adjoint.
    rewrite (logic_equiv_sepcon_comm emp
      ((EX y_callee_v x_callee_v retval_2,
        “ retval_2 = Zgcd a_pre b_pre ” &&
        “ a_pre * x_callee_v + b_pre * y_callee_v = Zgcd a_pre b_pre ” &&
        “ b_pre <> 0 ” && “ a_pre % (b_pre) <> 0 ” &&
        “ Zabs x_callee_v <= Zabs b_pre ÷ Zgcd a_pre b_pre ” &&
        “ Zabs y_callee_v <= Zabs a_pre ÷ Zgcd a_pre b_pre ” &&
        x_pre # Int |-> x_callee_v ** y_pre # Int |-> y_callee_v)
       || (EX y_callee_v_2 x_callee_v_2 retval_2,
           “ retval_2 = Zgcd a_pre b_pre ” &&
           “ a_pre * x_callee_v_2 + b_pre * y_callee_v_2 = Zgcd a_pre b_pre ” &&
           “ b_pre <> 0 ” && “ a_pre % (b_pre) = 0 ” &&
           “ x_callee_v_2 = 0 ” && “ Zabs y_callee_v_2 <= 1 ” &&
           x_pre # Int |-> x_callee_v_2 ** y_pre # Int |-> y_callee_v_2)
       || (EX y_callee_v_3 x_callee_v_3 retval_2,
           “ retval_2 = Zgcd a_pre b_pre ” &&
           “ a_pre * x_callee_v_3 + b_pre * y_callee_v_3 = Zgcd a_pre b_pre ” &&
           “ b_pre = 0 ” && “ Zabs x_callee_v_3 <= 1 ” &&
           “ y_callee_v_3 = 0 ” &&
           x_pre # Int |-> x_callee_v_3 ** y_pre # Int |-> y_callee_v_3))).
    rewrite sepcon_emp_equiv.
    apply derivable1_orp_elim.
    + apply derivable1_orp_elim.
      * Intros y_callee_v x_callee_v retval_2.
        Exists y_callee_v.
        Exists x_callee_v.
        Exists retval_2.
        split_pure_spatial.
        -- cancel.
        -- split_pures.
           ++ dump_pre_spatial. exact H3.
           ++ dump_pre_spatial. exact H4.
      * Intros y_callee_v x_callee_v retval_2.
        Exists y_callee_v.
        Exists x_callee_v.
        Exists retval_2.
        split_pure_spatial.
        -- cancel.
        -- split_pures.
           ++ dump_pre_spatial. exact H3.
           ++ dump_pre_spatial. exact H4.
    + Intros y_callee_v x_callee_v retval_2.
      Exists y_callee_v.
      Exists x_callee_v.
      Exists retval_2.
      split_pure_spatial.
      * cancel.
      * split_pures.
        -- dump_pre_spatial. exact H3.
        -- dump_pre_spatial. exact H4.
  - split_pures.
    + dump_pre_spatial. exact H.
    + dump_pre_spatial. exact H0.
    + dump_pre_spatial. exact H1.
    + dump_pre_spatial. exact H2.
Qed.
