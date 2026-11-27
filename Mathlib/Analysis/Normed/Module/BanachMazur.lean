/-
Copyright (c) 2026 David Muñoz-Lahoz, Jesús Illescas-Fiorito. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Muñoz-Lahoz, Jesús Illescas-Fiorito
-/
module

public import Mathlib.Analysis.Normed.Lp.lpHolder
public import Mathlib.Analysis.Normed.Operator.Mul

import Mathlib.Analysis.Normed.Operator.Banach

/-!
# The Banach-Mazur theorem

## Overview

## Main definitions

## Main results

## References

-- J: Beware that after the last line in references, no line-jump should be given!
-/

open Set TopologicalSpace Metric ContinuousLinearMap
-- J: I'm adding Pointwise to be able to write `(‖x‖ : 𝕜) • ball (0 : X) 1`. We
-- needd to do this instead of `ball (0 : X) (‖x‖ : 𝕜)` because for `x = 0` the latter
-- ''ball'' would be `∅`, instead of `{0}`.
open scoped lp ENNReal NNReal Pointwise

@[expose] public section

noncomputable section

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
variable {ι : Type*}

namespace BanachMazur

variable (𝕜) in
/-- A bounded family `x : ℓ^∞(ι, X)` induces a continuous linear map `ℓ¹(ι, 𝕜) →L[𝕜] X`,
given by `f ↦ ∑' i, f i • x i`. -/
def map : ℓ^∞(ι, X) →L[𝕜] ℓ¹(ι, 𝕜) →L[𝕜] X :=
  lp.dualPairing ∞ 1 (fun _ ↦ (toSpanSingletonLIE 𝕜 X : X →L[𝕜] 𝕜 →L[𝕜] X)) (K := 1)
    fun _ ↦ (toSpanSingletonLIE 𝕜 X).toLinearIsometry.norm_toContinuousLinearMap_le

theorem map_apply (x : ℓ^∞(ι, X)) (f : ℓ¹(ι, 𝕜)) : map 𝕜 x f = ∑' i, f i • x i :=
  rfl

theorem norm_map_le : ‖map 𝕜 (ι := ι) (X := X)‖ ≤ 1 :=
  (lp.norm_dualPairing (p := ∞) (q := 1) _ _).trans_eq NNReal.coe_one

theorem norm_map_apply_le (x : ℓ^∞(ι, X)) : ‖map 𝕜 x‖ ≤ ‖x‖ := by
  simpa using (map 𝕜 (ι := ι) (X := X)).le_of_opNorm_le norm_map_le x

@[simp]
theorem map_single [DecidableEq ι] (x : ℓ^∞(ι, X)) (i : ι) (a : 𝕜) :
    map 𝕜 x (lp.single 1 i a) = a • x i := by
  simp [map_apply, Pi.single_apply, ite_smul, tsum_ite_eq]

/-- The **Generalized Banach-Mazur theorem**: if `range x` is dense in `‖x‖ • ball (0 : X) 1`,
then `map 𝕜 x` maps the open unit ball of `ℓ¹(ι, 𝕜)` onto `‖x‖ ball 0 1` in `X`. -/
theorem map_surjective (x : ℓ^∞(ι, X))
    (hd : (‖x‖ : 𝕜) • ball (0 : X) 1 ⊆ closure (range x)) :
    (map 𝕜 x)'' ball 0 1 = (‖x‖ : 𝕜) • ball (0 : X) 1 := by
  classical
  -- J : Mathlib/Basic/Logic/Basic.lean, line 246, explicitely says that if some proof needs
  -- decidability, classical is prefered above the [DecidableEq ι] we would need here
  -- (to use lp.single). Also I've omitted the second rcases bullet since it seems Mathlib
  -- would prefer that.
  rcases eq_or_ne x 0 with rfl | hx
  · simp [Set.singleton_zero]
  have : (map 𝕜 x)'' ball 0 1 ⊆ (‖x‖ : 𝕜) • ball (0 : X) 1 := by
    rintro _ ⟨z, hz, rfl⟩
    rw [smul_unitBall (by simpa using hx), RCLike.norm_ofReal, abs_norm, mem_ball_zero_iff]
    calc
      ‖map 𝕜 x z‖ ≤ ‖x‖ * ‖z‖ := (map 𝕜 x).le_of_opNorm_le (norm_map_apply_le x) z
      _ < ‖x‖ := mul_lt_of_lt_one_right (norm_pos_iff.mpr hx) (mem_ball_zero_iff.mp hz)
  refine Set.Subset.antisymm this ?_
  have approx (ε : ℝ) (hε_pos : 0 < ε) (y : X) :
      ∃ z : ℓ¹(ι, 𝕜), dist (map 𝕜 x z) y ≤ ε * ‖y‖ ∧ ‖z‖ ≤ ‖x‖⁻¹ * ‖y‖ := by
    rcases eq_or_ne y 0 with rfl | hy
    · exact ⟨0, by simp⟩
    · let w : X := (‖y‖⁻¹ * ‖x‖ : 𝕜) • y
      obtain ⟨i, hi⟩ : ∃ i : ι, ‖x i - w‖ < ε * ‖x‖ := by sorry
      refine ⟨lp.single 1 i (‖x‖⁻¹ * ‖y‖ : 𝕜), ?_, ?_⟩
      · rw [map_single, dist_eq_norm]
        apply (mul_le_mul_iff_right₀
          (mul_pos (inv_pos.mpr (norm_pos_iff.mpr hy)) (norm_pos_iff.mpr hx))).mp
        conv_lhs =>
          rw [show ‖y‖⁻¹ * ‖x‖ = ‖(‖y‖⁻¹ * ‖x‖ : 𝕜)‖ by simp, ← norm_smul]
          simp [smul_sub, smul_smul, mul_assoc, hx, hy]
          rw [← RCLike.ofReal_inv]
        conv_rhs => simp [mul_comm, mul_left_comm, mul_assoc, hy]
        exact hi.le
      · simp [lp.norm_single]
  intro y hy
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (1 / 2 : ℝ) ^ n < 1 - ‖x‖⁻¹ * ‖y‖ := by
    apply exists_pow_lt_of_lt_one ?_ (by norm_num)
    have : ‖y‖ < ‖x‖ := by
      refine mem_ball_zero_iff.mp ?_
      simpa [smul_unitBall, hx] using hy
    rwa [sub_pos, inv_mul_lt_iff₀ (norm_pos_iff.mpr hx), mul_one]
  have hn_lt : (1 / 2 : ℝ) ^ n < 1 := hn.trans_le (sub_le_self _ (by positivity))
  obtain ⟨z, hz, hz_norm⟩ := (map 𝕜 x).exists_preimage_norm_le_of_approx
    ((1 / 2 : ℝ) ^ n) (‖x‖⁻¹) (by positivity) hn_lt (by positivity) (approx _ (by positivity)) y
  refine ⟨z, ?_, hz⟩
  rw [mem_ball_zero_iff]
  calc
    ‖z‖ ≤ ‖x‖⁻¹ / (1 - (1 / 2 : ℝ) ^ n) * ‖y‖ := hz_norm
    _ = (‖x‖⁻¹ * ‖y‖) / (1 - (1 / 2 : ℝ) ^ n) := div_mul_eq_mul_div _ _ _
    _ < 1 := (div_lt_one (sub_pos.mpr hn_lt)).2 (lt_sub_comm.mp hn)

/-- The **Classical Banach-Mazur theorem**: If `X` is a separable Banach space,
then there exists an operator `ℓ¹ →L[𝕜] X` sending the unit ball onto the unit ball. -/
theorem exists_surjective_of_separableSpace [SeparableSpace X] :
    ∃ T : ℓ¹(ℕ, 𝕜) →L[𝕜] X, T '' ball 0 1 = ball 0 1 := by
  rcases subsingleton_or_nontrivial X with hX | hX
  · exact ⟨0, by simp [Subsingleton.eq_univ_of_nonempty]⟩
  · -- we will use map 𝕜 x, where x is a dense subset of ball 0 1
    have : Nonempty (ball (0 : X) 1) := ⟨⟨0, mem_ball_self one_pos⟩⟩
    obtain ⟨v, hv⟩ := exists_dense_seq (ball (0 : X) 1)
    have hle (n : ℕ) : ‖(v n : X)‖ ≤ 1 := (mem_ball_zero_iff.1 (v n).2).le
    let x : ℓ^∞(ℕ, X) := ⟨fun n ↦ v n, memℓp_infty ⟨1, forall_mem_range.2 hle⟩⟩
    have x_ball : ball 0 1 ⊆ closure (range x) := by
      have := Subtype.dense_iff.1 hv
      rwa [← range_comp] at this
    have x_norm : ‖x‖ = 1 := by
      sorry
    exact ⟨map 𝕜 x, x_norm ▸ map_surjective (𝕜 := 𝕜) x (x_norm ▸ x_ball)⟩

-- Preguntas: usar lp.dualPairing o nueva API. Dónde colocar este archivo y cómo llamarlo.
-- Refactor de Banach.lean. Cómo organizar los commits.
-- ToDo: escribir docstring inicial siguiendo el estilo de mathlib; revisar guía de estilo de
-- mathlib y comprobar que el código la cumple; comprobar nombres según mathlib
end BanachMazur
