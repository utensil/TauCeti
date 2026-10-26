/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth

/-!
# Smooth pullback on model spaces

This module connects the smooth-form pullback carrier with the flat pullback formula on model
spaces.  The result lets a smooth-form consumer use the Fréchet derivative formula without
unbundling the smooth form first.

The proof is the smooth-carrier specialization of the rough-form model-space identity; no new
pullback construction is introduced here.
-/

public section

noncomputable section

open scoped Manifold ContDiff

namespace TauCeti

variable {E E' F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

namespace SmoothForm

/-- On model spaces, the smooth pullback is the flat pullback by the Fréchet derivative. -/
theorem mpullback_eq_flat (f : E → E')
    (hf : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E')) ∞ f)
    (φ : SmoothForm (𝓘(ℝ, E')) E' F k) :
    (mpullback f hf φ : RoughForm (𝓘(ℝ, E)) E F k) =
      fun x ↦ (φ.1 (f x)).compContinuousLinearMap (fderiv ℝ f x) := by
  rw [coe_mpullback]
  exact TauCeti.mpullback_eq_flat f φ.1

end SmoothForm

end TauCeti

end
