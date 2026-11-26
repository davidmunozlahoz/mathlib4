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
open scoped lp ENNReal NNReal

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

/-- The **Generalized Banach-Mazur theorem**: if range x is dense in ball 0 ‖x‖,
then map 𝕜 x maps the open unit ball of ℓ¹(ι, 𝕜) onto ball 0 ‖x‖.
-/
theorem map_surjective (x : ℓ^∞(ι, X))
    (hd : ball 0 ‖x‖ ⊆ closure (range x)) : (map 𝕜 x)'' ball 0 1 = ball 0 ‖x‖ := by
  have approx (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1) (y : X) :
      ∃ f : ℓ¹(ι, 𝕜), dist (map 𝕜 x f) y ≤ 1 / 2 * ‖y‖ ∧ ‖f‖ ≤ ‖x‖⁻¹ * ‖y‖ := by
    sorry
  sorry

/-- The **Classical Banach-Mazur theorem**: If `X` is a separable Banach space, then there exists an
operator `ℓ¹ →L[𝕜] X` sending the unit ball onto the unit ball. -/
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

-- Preguntas: usar lp.dualPairing o nueva API. Dónde colocar este archivo y cómo llamarlo. Refactor de Banach.lean. Cómo organizar los commits.
-- ToDo: escribir docstring inicial siguiendo el estilo de mathlib; revisar guía de estilo de mathlib y comprobar que el código la cumple; comprobar nombres según mathlib
end BanachMazur
