/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Smooth.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.ContinuousAlternatingMap
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Analysis.Calculus.DifferentialForm.Wedge

/-!
# Smooth paired wedges of bundle-valued differential forms

A smooth section of the bundle of continuous bilinear maps is the coefficient
interface for pairing bundle-valued forms.  This file records that interface and
proves the coordinate identity needed to establish smoothness of the resulting
paired wedge.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 14.
* Mathlib's smooth hom-bundle construction in `Geometry/Manifold/VectorBundle/Hom.lean`.
-/

public section

noncomputable section

open Bundle Filter
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E H M F₁ F₂ F₃ : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
  [IsManifold I 1 M]
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  [NormedAddCommGroup F₃] [NormedSpace ℝ F₃]
  {V₁ V₂ V₃ : M → Type*}
  [∀ x, AddCommGroup (V₁ x)] [∀ x, Module ℝ (V₁ x)] [∀ x, TopologicalSpace (V₁ x)]
  [TopologicalSpace (TotalSpace F₁ V₁)] [FiberBundle F₁ V₁] [VectorBundle ℝ F₁ V₁]
  [∀ x, AddCommGroup (V₂ x)] [∀ x, Module ℝ (V₂ x)] [∀ x, TopologicalSpace (V₂ x)]
  [TopologicalSpace (TotalSpace F₂ V₂)] [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂]
  [∀ x, AddCommGroup (V₃ x)] [∀ x, Module ℝ (V₃ x)] [∀ x, TopologicalSpace (V₃ x)]
  [TopologicalSpace (TotalSpace F₃ V₃)] [FiberBundle F₃ V₃] [VectorBundle ℝ F₃ V₃]
  [∀ x, IsTopologicalAddGroup (V₁ x)] [∀ x, ContinuousSMul ℝ (V₁ x)]
  [∀ x, IsTopologicalAddGroup (V₂ x)] [∀ x, ContinuousSMul ℝ (V₂ x)]
  [∀ x, IsTopologicalAddGroup (V₃ x)] [∀ x, ContinuousSMul ℝ (V₃ x)]
  [ContMDiffVectorBundle ∞ F₁ V₁ I] [ContMDiffVectorBundle ∞ F₂ V₂ I]
  [ContMDiffVectorBundle ∞ F₃ V₃ I]
  {k l : ℕ}

/-- A smooth fibrewise bilinear pairing between three vector bundles over `M`. -/
structure SmoothBundlePairing where
  /-- The fibrewise continuous bilinear map defining the pairing. -/
  toFun : (x : M) → V₁ x →L[ℝ] V₂ x →L[ℝ] V₃ x
  /-- Continuity of the bilinear evaluation in the possibly non-normed fibre topologies. -/
  continuous₂ : ∀ x, Continuous (Function.uncurry fun a b ↦ toFun x a b)
  /-- Smoothness of the pairing as a section of the bundle of bilinear maps. -/
  smooth : ContMDiff I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂ →L[ℝ] F₃)) ∞
    (fun x ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂ →L[ℝ] F₃) x (toFun x))

/-- Evaluate a smooth bundle pairing in a base fibre. -/
instance : CoeFun (SmoothBundlePairing (I := I) (F₁ := F₁) (F₂ := F₂) (F₃ := F₃)
    (V₁ := V₁) (V₂ := V₂) (V₃ := V₃)) (fun _ ↦ (x : M) → V₁ x →L[ℝ] V₂ x →L[ℝ] V₃ x) :=
  ⟨SmoothBundlePairing.toFun⟩

omit [IsManifold I 1 M]
  [∀ x, IsTopologicalAddGroup (V₁ x)] [∀ x, ContinuousSMul ℝ (V₁ x)]
  [∀ x, IsTopologicalAddGroup (V₂ x)] [∀ x, ContinuousSMul ℝ (V₂ x)]
  [ContMDiffVectorBundle ∞ F₁ V₁ I] [ContMDiffVectorBundle ∞ F₂ V₂ I]
  [ContMDiffVectorBundle ∞ F₃ V₃ I] in
@[ext]
theorem SmoothBundlePairing.ext {μ ν : SmoothBundlePairing (I := I) (F₁ := F₁) (F₂ := F₂)
    (F₃ := F₃) (V₁ := V₁) (V₂ := V₂) (V₃ := V₃)}
    (h : ∀ x, μ x = ν x) : μ = ν := by
  cases μ
  cases ν
  simp only [SmoothBundlePairing.mk.injEq]
  exact funext h


omit [∀ x, IsTopologicalAddGroup (V₁ x)] [∀ x, ContinuousSMul ℝ (V₁ x)]
  [∀ x, IsTopologicalAddGroup (V₂ x)] [∀ x, ContinuousSMul ℝ (V₂ x)]
  [ContMDiffVectorBundle ∞ F₁ V₁ I] [ContMDiffVectorBundle ∞ F₂ V₂ I]
  [ContMDiffVectorBundle ∞ F₃ V₃ I] in
/-- In compatible bundle coordinates, a fibrewise paired wedge is the paired wedge
of the coordinate forms and the coordinate pairing. -/
theorem bundleWedgeWith_inCoordinates
    (μ : SmoothBundlePairing (I := I) (F₁ := F₁) (F₂ := F₂) (F₃ := F₃)
      (V₁ := V₁) (V₂ := V₂) (V₃ := V₃))
    (φ : RoughBundleForm I M V₁ k) (ψ : RoughBundleForm I M V₂ l) (x₀ y : M)
    (hyT : y ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (hy1 : y ∈ (trivializationAt F₁ V₁ x₀).baseSet)
    (hy2 : y ∈ (trivializationAt F₂ V₂ x₀).baseSet)
    (hy3 : y ∈ (trivializationAt F₃ V₃ x₀).baseSet) :
    ContinuousAlternatingMap.inCoordinates E F₃ x₀ y x₀ y
        (bundleWedgeWith (fun x ↦ μ x) (fun x ↦ μ.continuous₂ x) φ ψ y) =
      ContinuousAlternatingMap.pairedWedge
        (ContinuousLinearMap.inCoordinates F₁ V₁ (F₂ →L[ℝ] F₃)
          (fun x ↦ V₂ x →L[ℝ] V₃ x) x₀ y x₀ y (μ y))
        (ContinuousLinearMap.continuous₂ _)
        (ContinuousAlternatingMap.inCoordinates E F₁ x₀ y x₀ y (φ y))
        (ContinuousAlternatingMap.inCoordinates E F₂ x₀ y x₀ y (ψ y)) := by
  rw [ContinuousAlternatingMap.inCoordinates_eq E F₃ (x₀ := x₀) (x := y)
    (y₀ := x₀) (y := y) hyT hy3]
  rw [ContinuousAlternatingMap.inCoordinates_eq E F₁ (x₀ := x₀) (x := y)
    (y₀ := x₀) (y := y) hyT hy1]
  rw [ContinuousAlternatingMap.inCoordinates_eq E F₂ (x₀ := x₀) (x := y)
    (y₀ := x₀) (y := y) hyT hy2]
  apply ContinuousAlternatingMap.ext
  intro v
  simp only [bundleWedgeWith_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousLinearMap.compContinuousAlternatingMap_coe,
    Function.comp_apply]
  rw [ContinuousAlternatingMap.pairedWedge_apply]
  simp_rw [inCoordinates_apply_eq₂ hy1 hy2 hy3]
  simp only [mul_inv_rev, ContinuousLinearEquiv.coe_coe,
    Trivialization.continuousLinearEquivAt_symm_apply, map_smul, map_sum, map_zsmul_unit,
    Trivialization.continuousLinearEquivAt_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousLinearMap.compContinuousAlternatingMap_coe, Function.comp_apply]
  have h1 (z : V₁ y) : (trivializationAt F₁ V₁ x₀).symm y
      ((trivializationAt F₁ V₁ x₀) ⟨y, z⟩).2 = z :=
    (trivializationAt F₁ V₁ x₀).symm_apply_apply_mk hy1 z
  have h2 (z : V₂ y) : (trivializationAt F₂ V₂ x₀).symm y
      ((trivializationAt F₂ V₂ x₀) ⟨y, z⟩).2 = z :=
    (trivializationAt F₂ V₂ x₀).symm_apply_apply_mk hy2 z
  apply congrArg (fun z => ((l.factorial : ℝ)⁻¹ * (k.factorial : ℝ)⁻¹) • z)
  apply Finset.sum_congr rfl
  intro σ hσ
  apply congrArg (fun z => Equiv.Perm.sign σ • z)
  rw [Bundle.Trivialization.coe_linearMapAt_of_mem _ hy3]
  simp only [h1, h2]
  rfl


namespace SmoothBundleForm

/-- The paired wedge of smooth bundle-valued forms along a smooth fibrewise pairing. -/
def wedgeWith (μ : SmoothBundlePairing (I := I) (F₁ := F₁) (F₂ := F₂) (F₃ := F₃)
    (V₁ := V₁) (V₂ := V₂) (V₃ := V₃))
    (φ : SmoothBundleForm I F₁ V₁ k) (ψ : SmoothBundleForm I F₂ V₂ l) :
    SmoothBundleForm I F₃ V₃ (k + l) :=
  ⟨bundleWedgeWith (fun x ↦ μ x) (fun x ↦ μ.continuous₂ x) φ.1 ψ.1, by
    apply mem_smoothBundleForms.mpr
    rw [isSmoothBundleForm_def]
    intro x
    apply (contMDiffAt_continuousAlternatingMap_bundle _).mpr
    refine ⟨contMDiffAt_id, ?_⟩
    let : NormedAddCommGroup
        ((E [⋀^Fin l]→L[ℝ] F₂) →L[ℝ] (E [⋀^Fin (k + l)]→L[ℝ] F₃)) := inferInstance
    let : NormedSpace ℝ
        ((E [⋀^Fin l]→L[ℝ] F₂) →L[ℝ] (E [⋀^Fin (k + l)]→L[ℝ] F₃)) := inferInstance
    let : NormedAddCommGroup
        ((E [⋀^Fin k]→L[ℝ] F₁) →L[ℝ] (E [⋀^Fin l]→L[ℝ] F₂) →L[ℝ]
          E [⋀^Fin (k + l)]→L[ℝ] F₃) := inferInstance
    let : NormedSpace ℝ
        ((E [⋀^Fin k]→L[ℝ] F₁) →L[ℝ] (E [⋀^Fin l]→L[ℝ] F₂) →L[ℝ]
          E [⋀^Fin (k + l)]→L[ℝ] F₃) := inferInstance
    have hφ' := (isSmoothBundleForm_def ∞ φ.1).mp
      (mem_smoothBundleForms.mp φ.2) x
    have hψ' := (isSmoothBundleForm_def ∞ ψ.1).mp
      (mem_smoothBundleForms.mp ψ.2) x
    have hφ := (contMDiffAt_continuousAlternatingMap_bundle _).mp hφ'
    have hψ := (contMDiffAt_continuousAlternatingMap_bundle _).mp hψ'
    have hμ := (contMDiffAt_hom_bundle (f := fun y ↦
      TotalSpace.mk' (F₁ →L[ℝ] F₂ →L[ℝ] F₃) y (μ y))).mp (μ.smooth x)
    have h := (contMDiffAt_const
      (c := ContinuousAlternatingMap.pairedWedgeCLM (E := E) (k := k) (l := l))).clm_apply
        hμ.2 |>.clm_apply hφ.2 |>.clm_apply hψ.2
    have hT : ∀ᶠ y in 𝓝 x,
        y ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
      (trivializationAt E (TangentSpace I) x).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt E (TangentSpace I) x)
    have h1 : ∀ᶠ y in 𝓝 x, y ∈ (trivializationAt F₁ V₁ x).baseSet :=
      (trivializationAt F₁ V₁ x).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt F₁ V₁ x)
    have h2 : ∀ᶠ y in 𝓝 x, y ∈ (trivializationAt F₂ V₂ x).baseSet :=
      (trivializationAt F₂ V₂ x).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt F₂ V₂ x)
    have h3 : ∀ᶠ y in 𝓝 x, y ∈ (trivializationAt F₃ V₃ x).baseSet :=
      (trivializationAt F₃ V₃ x).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt F₃ V₃ x)
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [hT, h1, h2, h3] with y hyT hy1 hy2 hy3
    simpa only [ContinuousAlternatingMap.pairedWedgeCLM_apply] using
      (bundleWedgeWith_inCoordinates μ φ.1 ψ.1 x y hyT hy1 hy2 hy3)
    ⟩

omit [ContMDiffVectorBundle ∞ F₁ V₁ I] [ContMDiffVectorBundle ∞ F₂ V₂ I]
  [ContMDiffVectorBundle ∞ F₃ V₃ I] in
/-- The smooth paired wedge forgets to the rough bundle-valued paired wedge. -/
@[simp] theorem coe_wedgeWith
    (μ : SmoothBundlePairing (I := I) (F₁ := F₁) (F₂ := F₂) (F₃ := F₃)
      (V₁ := V₁) (V₂ := V₂) (V₃ := V₃))
    (φ : SmoothBundleForm I F₁ V₁ k) (ψ : SmoothBundleForm I F₂ V₂ l) :
    (wedgeWith μ φ ψ : RoughBundleForm I M V₃ (k + l)) =
      bundleWedgeWith (fun x ↦ μ x) (fun x ↦ μ.continuous₂ x) φ.1 ψ.1 := by
  rfl

omit [ContMDiffVectorBundle ∞ F₁ V₁ I] [ContMDiffVectorBundle ∞ F₂ V₂ I]
  [ContMDiffVectorBundle ∞ F₃ V₃ I] in
/-- Evaluation of the smooth bundle-valued paired wedge. -/
theorem wedgeWith_apply
    (μ : SmoothBundlePairing (I := I) (F₁ := F₁) (F₂ := F₂) (F₃ := F₃)
      (V₁ := V₁) (V₂ := V₂) (V₃ := V₃))
    (φ : SmoothBundleForm I F₁ V₁ k) (ψ : SmoothBundleForm I F₂ V₂ l)
    (x : M) (v : Fin (k + l) → TangentSpace I x) :
    (wedgeWith μ φ ψ).1 x v =
      (((k.factorial : ℝ) * (l.factorial : ℝ))⁻¹) •
        ∑ σ : Equiv.Perm (Fin (k + l)), Equiv.Perm.sign σ •
          μ x (φ.1 x (fun i ↦ v (σ (Fin.castAdd l i))) )
            (ψ.1 x (fun j ↦ v (σ (Fin.natAdd k j)))) := by
  rw [coe_wedgeWith, bundleWedgeWith_apply]

end SmoothBundleForm

end TauCeti
