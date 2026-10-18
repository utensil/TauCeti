/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Smooth.Basic

/-!
# Pullback and smooth wedge products

The smooth fixed-coefficient differential-form carrier inherits the pullback compatibility of the
underlying rough forms.  These bundled identities make smooth pullback a morphism of the paired
wedge algebra, and hence supply the naturality interface used by de Rham constructions.
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace TauCeti

variable {E H M E' H' M' F₁ F₂ F₃ : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  [TopologicalSpace M'] [ChartedSpace H' M'] {I' : ModelWithCorners ℝ E' H'}
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  [NormedAddCommGroup F₃] [NormedSpace ℝ F₃]
  [IsManifold I 1 M] [IsManifold I' 1 M'] {k l : ℕ}

namespace SmoothForm

/-- Smooth pullback preserves the paired wedge of fixed-coefficient forms. -/
theorem mpullback_wedgeWith (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃) (f : M' → M)
    (hf : ContMDiff I' I ∞ f) (φ : SmoothForm I M F₁ k) (ψ : SmoothForm I M F₂ l) :
    mpullback f hf (wedgeWith μ φ ψ) =
      wedgeWith μ (mpullback f hf φ) (mpullback f hf ψ) := by
  apply Subtype.ext
  rw [coe_mpullback, coe_wedgeWith, coe_wedgeWith, coe_mpullback, coe_mpullback]
  exact TauCeti.mpullback_wedgeWith μ f (φ : RoughForm I M F₁ k) (ψ : RoughForm I M F₂ l)

/-- Smooth pullback preserves the real-valued wedge. -/
theorem mpullback_wedge (f : M' → M) (hf : ContMDiff I' I ∞ f)
    (φ : SmoothForm I M ℝ k) (ψ : SmoothForm I M ℝ l) :
    mpullback f hf (wedge φ ψ) =
      wedge (mpullback f hf φ) (mpullback f hf ψ) := by
  rw [wedge_def, wedge_def]
  exact mpullback_wedgeWith (ContinuousLinearMap.mul ℝ ℝ) f hf φ ψ

end SmoothForm

end TauCeti
