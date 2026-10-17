/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Basic

/-!
# Interior products of rough differential forms

This file lifts the norm-free interior product on continuous alternating maps to rough forms.
The interior product inserts a tangent vector field in the first slot, and its antiderivation law
for a paired wedge is inherited pointwise from `ContinuousAlternatingMap.curryLeftTopological`.
-/

public section

noncomputable section

namespace TauCeti

variable {E H M F₁ F₂ F₃ : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
  [SeminormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [SeminormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  [SeminormedAddCommGroup F₃] [NormedSpace ℝ F₃]
  {k l : ℕ}

namespace RoughForm

/-- Insert a tangent vector field into the first slot of a rough form. -/
def curryLeftTopological (V : (x : M) → TangentSpace I x)
    (φ : RoughForm I M F₁ (k + 1)) : RoughForm I M F₁ k :=
  fun x ↦ ContinuousAlternatingMap.curryLeftTopological (φ x) (V x)

@[simp]
theorem curryLeftTopological_apply (V : (x : M) → TangentSpace I x)
    (φ : RoughForm I M F₁ (k + 1)) (x : M) :
    curryLeftTopological V φ x =
      ContinuousAlternatingMap.curryLeftTopological (φ x) (V x) :=
  by
    change (fun y ↦ ContinuousAlternatingMap.curryLeftTopological (φ y) (V y)) x = _
    rfl

/-- The interior product is an antiderivation of a paired rough-form wedge.

The first term is reassociated from degree `k + (l + 1)` to `k + 1 + l` by the canonical
`Fin.cast`; this is the same degree convention as the alternating-map theorem underneath. -/
theorem curryLeftTopological_wedgeWith
    [IsTopologicalAddGroup F₁] [ContinuousConstSMul ℝ F₁]
    [IsTopologicalAddGroup F₂] [ContinuousConstSMul ℝ F₂]
    (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (φ : RoughForm I M F₁ (k + 1)) (ψ : RoughForm I M F₂ (l + 1))
    (V : (x : M) → TangentSpace I x) (x : M)
    (w : Fin (k + 1 + l) → TangentSpace I x) :
    curryLeftTopological V (RoughForm.wedgeWith (k := k + 1) (l := l + 1) μ φ ψ) x w =
      RoughForm.wedgeWith (k := k) (l := l + 1) μ (φ.curryLeftTopological V) ψ x
          (w ∘ Fin.cast (show k + (l + 1) = k + 1 + l by omega)) +
        (-1 : ℝ) ^ (k + 1) •
          RoughForm.wedgeWith (k := k + 1) (l := l) μ φ (ψ.curryLeftTopological V) x w := by
  simpa only [curryLeftTopological_apply, RoughForm.wedgeWith_apply'] using
    (ContinuousAlternatingMap.curryLeftTopological_pairedWedge
      (E := TangentSpace I x) μ μ.continuous₂ (φ x) (ψ x) (V x) w)

end RoughForm

end TauCeti
