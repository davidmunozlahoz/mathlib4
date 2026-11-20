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

-/

open Set TopologicalSpace Metric
open scoped lp ENNReal NNReal

@[expose] public section

noncomputable section

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
variable {ι : Type*}

namespace BanachMazur

variable (𝕜) in
open ContinuousLinearMap in
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

-- ToDo: probably should make this stronger to says that it sends the ball to the ball;
-- it shouldn't be difficult using the approx and ContinuousLinearMap.exists_preimage_norm_le_of_approx
theorem map_surjective (x : ℓ^∞(ι, X)) (hx : x ≠ 0)
    (hd : ball 0 ‖x‖ ⊆ closure (range x)) : Function.Surjective (map 𝕜 x) := by
  have approx (y : X) :
      ∃ f : ℓ¹(ι, 𝕜), dist (map 𝕜 x f) y ≤ 1 / 2 * ‖y‖ ∧ ‖f‖ ≤ ‖x‖⁻¹ * ‖y‖ := by
    -- ToDo: reescribir or revisar con mucho cuidado.
    classical
    rcases eq_or_ne y 0 with rfl | hy
    · exact ⟨0, by simp⟩
    have hx₀ : 0 < ‖x‖ := norm_pos_iff.mpr hx
    set a : 𝕜 := ((‖y‖ / ‖x‖ : ℝ) : 𝕜)
    have ha : ‖a‖ = ‖y‖ / ‖x‖ := by simp [a]
    have ha₀ : a ≠ 0 := by simp [a, hy, hx]
    have hz : a⁻¹ • y ∈ closure (range x) := hd <| by
      sorry
    obtain ⟨i, hi⟩ := Metric.mem_closure_range_iff.mp hz (‖x‖ / 2) (by positivity)
    refine ⟨a • lp.single 1 i 1, ?_, ?_⟩
    · calc dist (map 𝕜 x (a • lp.single 1 i 1)) y = dist (a • x i) (a • a⁻¹ • y) := by
            simp [smul_inv_smul₀ ha₀]
        _ = ‖a‖ * dist (a⁻¹ • y) (x i) := by rw [dist_smul₀, dist_comm]
        _ ≤ ‖y‖ / ‖x‖ * (‖x‖ / 2) := by rw [ha]; gcongr
        _ = 1 / 2 * ‖y‖ := by field_simp
    · simp [norm_smul, ha, div_eq_inv_mul]
  obtain ⟨C, -, hC⟩ :=
    ContinuousLinearMap.exists_preimage_norm_le_of_approx (map 𝕜 x) (by positivity) approx
  exact fun y ↦ (hC y).imp fun _ ↦ And.left

/-- The Banach-Mazur theorem: If `X` is a separable Banach space, then there exists an
operator `ℓ¹ →L[𝕜] X` sending the unit ball to the unit ball. -/
theorem exists_surjective_of_separableSpace [SeparableSpace X] :
    ∃ T : ℓ¹(ℕ, 𝕜) →L[𝕜] X, T '' ball 0 1 = ball 0 1 := by
  sorry

-- Preguntas: usar lp.dualPairing o nueva API. Dónde colocar este archivo y cómo llamarlo. Refactor de Banach.lean. Cómo organizar los commits.
-- ToDo: escribir docstring inicial siguiendo el estilo de mathlib; revisar guía de estilo de mathlib y comprobar que el código la cumple; comprobar nombres según mathlib
end BanachMazur
