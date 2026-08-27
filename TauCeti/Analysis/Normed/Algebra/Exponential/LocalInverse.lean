/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# A local inverse for the exponential in a Banach algebra

The exponential of a Banach algebra has derivative the identity at zero.  The inverse function
theorem therefore restricts it to a local homeomorphism from a neighborhood of `0` to a
neighborhood of `1`.  This file packages that local homeomorphism and its inverse, the logarithm
near `1`.

Unlike a logarithm defined by a power series on a prescribed ball, this logarithm is characterized
by being the inverse of exponential on the neighborhoods selected by the inverse function theorem.
Its values outside the target of `NormedSpace.expOpenPartialHomeomorph` carry no logarithmic
meaning.

## Main declarations

* `NormedSpace.expOpenPartialHomeomorph`: exponential restricted to neighborhoods of `0` and `1`.
* `NormedSpace.logNearOne`: its local inverse.
* `NormedSpace.analyticAt_logNearOne`: the local logarithm is analytic at `1`.
* `NormedSpace.eventually_logNearOne_exp` and `NormedSpace.eventually_exp_logNearOne`: the two
  local inverse equations.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 3, "Baker--Campbell--Hausdorff".
-/

public section

open Filter Topology

open scoped ContDiff

noncomputable section

namespace NormedSpace

variable {𝕂 A : Type*} [RCLike 𝕂] [NormedRing A] [NormedAlgebra 𝕂 A] [CompleteSpace A]

private theorem hasStrictFDerivAt_exp_zero_equiv :
    HasStrictFDerivAt (exp : A → A)
      ((ContinuousLinearEquiv.refl 𝕂 A : A ≃L[𝕂] A) : A →L[𝕂] A) 0 := by
  convert (hasStrictFDerivAt_exp_zero (𝕂 := 𝕂) (𝔸 := A)) using 1
  ext x
  simp

/-- Exponential restricted to the neighborhoods of `0` and `1` selected by the inverse function
theorem. -/
noncomputable def expOpenPartialHomeomorph : OpenPartialHomeomorph A A :=
  (hasStrictFDerivAt_exp_zero_equiv (𝕂 := 𝕂) (A := A)).toOpenPartialHomeomorph exp

/-- The forward map of the local exponential homeomorphism is `NormedSpace.exp`. -/
@[simp]
theorem expOpenPartialHomeomorph_apply (x : A) :
    expOpenPartialHomeomorph (𝕂 := 𝕂) (A := A) x = exp x := by
  rfl

/-- Zero belongs to the source of the local exponential homeomorphism. -/
theorem zero_mem_expOpenPartialHomeomorph_source :
    0 ∈ (expOpenPartialHomeomorph (𝕂 := 𝕂) (A := A)).source :=
  (hasStrictFDerivAt_exp_zero_equiv (𝕂 := 𝕂) (A := A))
    |>.mem_toOpenPartialHomeomorph_source

/-- One belongs to the target of the local exponential homeomorphism. -/
theorem one_mem_expOpenPartialHomeomorph_target :
    1 ∈ (expOpenPartialHomeomorph (𝕂 := 𝕂) (A := A)).target := by
  rw [← exp_zero]
  exact (expOpenPartialHomeomorph (𝕂 := 𝕂) (A := A)).map_source
    zero_mem_expOpenPartialHomeomorph_source

/-- The local logarithm near one, defined as the inverse of the local exponential homeomorphism.
Its values outside the target neighborhood carry no logarithmic meaning. -/
noncomputable def logNearOne : A → A :=
  (expOpenPartialHomeomorph (𝕂 := 𝕂) (A := A)).symm

/-- The local logarithm is the inverse map of `NormedSpace.expOpenPartialHomeomorph`. -/
theorem logNearOne_apply (x : A) :
    logNearOne (𝕂 := 𝕂) x =
      (expOpenPartialHomeomorph (𝕂 := 𝕂) (A := A)).symm x := by
  rfl

/-- The local logarithm sends one to zero. -/
@[simp]
theorem logNearOne_one : logNearOne (𝕂 := 𝕂) (1 : A) = 0 := by
  rw [← exp_zero]
  exact (expOpenPartialHomeomorph (𝕂 := 𝕂) (A := A)).left_inv
    zero_mem_expOpenPartialHomeomorph_source

/-- Exponential maps the source of the local exponential homeomorphism into its target. -/
theorem exp_mem_expOpenPartialHomeomorph_target {x : A}
    (hx : x ∈ (expOpenPartialHomeomorph (𝕂 := 𝕂) (A := A)).source) :
    exp x ∈ (expOpenPartialHomeomorph (𝕂 := 𝕂) (A := A)).target := by
  rw [← expOpenPartialHomeomorph_apply (𝕂 := 𝕂)]
  exact (expOpenPartialHomeomorph (𝕂 := 𝕂) (A := A)).map_source hx

/-- The local logarithm maps the target of the local exponential homeomorphism into its source. -/
theorem logNearOne_mem_expOpenPartialHomeomorph_source {x : A}
    (hx : x ∈ (expOpenPartialHomeomorph (𝕂 := 𝕂) (A := A)).target) :
    logNearOne (𝕂 := 𝕂) x ∈
      (expOpenPartialHomeomorph (𝕂 := 𝕂) (A := A)).source := by
  exact (expOpenPartialHomeomorph (𝕂 := 𝕂) (A := A)).map_target hx

/-- On the source of the local exponential homeomorphism, logarithm inverts exponential. -/
@[simp]
theorem logNearOne_exp_of_mem_source {x : A}
    (hx : x ∈ (expOpenPartialHomeomorph (𝕂 := 𝕂) (A := A)).source) :
    logNearOne (𝕂 := 𝕂) (exp x) = x := by
  exact (expOpenPartialHomeomorph (𝕂 := 𝕂) (A := A)).left_inv hx

/-- On the target of the local exponential homeomorphism, exponential inverts logarithm. -/
@[simp]
theorem exp_logNearOne_of_mem_target {x : A}
    (hx : x ∈ (expOpenPartialHomeomorph (𝕂 := 𝕂) (A := A)).target) :
    exp (logNearOne (𝕂 := 𝕂) x) = x := by
  exact (expOpenPartialHomeomorph (𝕂 := 𝕂) (A := A)).right_inv hx

/-- Near zero, the local logarithm is a left inverse to exponential. -/
theorem eventually_logNearOne_exp :
    ∀ᶠ x in 𝓝 (0 : A), logNearOne (𝕂 := 𝕂) (exp x) = x :=
  (expOpenPartialHomeomorph (𝕂 := 𝕂) (A := A)).eventually_left_inverse
    zero_mem_expOpenPartialHomeomorph_source

/-- Near one, exponential is a left inverse to the local logarithm. -/
theorem eventually_exp_logNearOne :
    ∀ᶠ x in 𝓝 (1 : A), exp (logNearOne (𝕂 := 𝕂) x) = x := by
  rw [← exp_zero]
  exact (expOpenPartialHomeomorph (𝕂 := 𝕂) (A := A)).eventually_right_inverse'
    zero_mem_expOpenPartialHomeomorph_source

/-- The local logarithm is analytic at one. -/
theorem analyticAt_logNearOne : AnalyticAt 𝕂 (logNearOne (𝕂 := 𝕂) : A → A) 1 := by
  let e := expOpenPartialHomeomorph (𝕂 := 𝕂) (A := A)
  have he : AnalyticAt 𝕂 e.symm 1 := by
    have hsource : (0 : A) ∈ e.source := zero_mem_expOpenPartialHomeomorph_source
    have he_apply : (e : A → A) = exp := by
      funext x
      exact expOpenPartialHomeomorph_apply (𝕂 := 𝕂) x
    have hexp : AnalyticAt 𝕂 (e : A → A) 0 := by
      rw [he_apply]
      exact exp_analytic (𝕂 := 𝕂) (0 : A)
    have hfderiv : fderiv 𝕂 (e : A → A) 0 =
        (ContinuousLinearEquiv.refl 𝕂 A : A ≃L[𝕂] A) := by
      rw [he_apply]
      exact (hasStrictFDerivAt_exp_zero_equiv (𝕂 := 𝕂) (A := A)).hasFDerivAt.fderiv
    simpa only [e, expOpenPartialHomeomorph_apply, exp_zero] using
      e.analyticAt_symm' hsource hexp hfderiv
  simpa only [logNearOne, e] using he

/-- The local logarithm is smooth at one. -/
theorem contDiffAt_logNearOne : ContDiffAt 𝕂 ∞ (logNearOne (𝕂 := 𝕂) : A → A) 1 :=
  analyticAt_logNearOne.contDiffAt

end NormedSpace
