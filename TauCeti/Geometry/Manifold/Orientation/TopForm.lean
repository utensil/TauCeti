/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Continuity
public import TauCeti.Topology.Algebra.Module.Alternating.TopDegree
public import TauCeti.Geometry.Manifold.Orientation.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame

/-!
# Orientations from nowhere-vanishing top forms

A nowhere-vanishing continuous top form selects the orientation on which it is positive.
This file supplies the first direction of the top-form/orientation correspondence used by
orientation-sensitive differential geometry. The fibrewise characterization is the local algebraic
part of J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Proposition 15.5.
-/

public section

noncomputable section

open Bundle Set Filter
open scoped Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

private def topFormBasis [IsManifold I 1 M] (x : M) :
    Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
  (trivializationAt E (TangentSpace I) x).basisAt (Module.finBasis ℝ E)
    (FiberBundle.mem_baseSet_trivializationAt' x)

/-- The fibre orientation selected by a nonzero top-degree form using the chart-local basis. -/
def topFormOrientationAt [IsManifold I 1 M]
    (φ : RoughForm I M ℝ (Module.finrank ℝ E)) (x : M) :
    _root_.Orientation ℝ (TangentSpace I x) (Fin (Module.finrank ℝ E)) :=
  if 0 < φ x (topFormBasis (I := I) x) then
    (topFormBasis (I := I) x).orientation
  else
    -(topFormBasis (I := I) x).orientation

/-- A basis is positive for `topFormOrientationAt` exactly when the form evaluates positively. -/
theorem topFormOrientationAt_spec [IsManifold I 1 M]
    {φ : RoughForm I M ℝ (Module.finrank ℝ E)} (x : M) (h0 : φ x ≠ 0)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x)) :
    b.orientation = topFormOrientationAt (I := I) φ x ↔ 0 < φ x b := by
  let b₀ := topFormBasis (I := I) x
  have hbase : φ x b₀ ≠ 0 := by
    intro hz
    apply h0
    ext v
    rw [ContinuousAlternatingMap.apply_eq_det_mul (φ x) b₀ v, hz, mul_zero]
    simp
  have hformula : φ x b = b₀.det b * φ x b₀ := by
    exact ContinuousAlternatingMap.apply_eq_det_mul (φ x) b₀ b
  have hformula' : φ x b₀ = b.det b₀ * φ x b := by
    exact ContinuousAlternatingMap.apply_eq_det_mul (φ x) b b₀
  by_cases hp : 0 < φ x b₀
  -- `topFormOrientationAt` is defined with the chart basis; expose that branch before
  -- applying the basis-orientation characterization.
  · change b.orientation = (if 0 < φ x b₀ then b₀.orientation else -b₀.orientation) ↔ _
    rw [ite_eq_left hp]
    have hor : b.orientation = b₀.orientation ↔ 0 < b₀.det b := by
      simpa only [eq_comm] using (b₀.orientation_eq_iff_det_pos b)
    rw [hor]
    constructor
    · intro hd
      rw [hformula]
      exact mul_pos hd hp
    · intro hb
      rw [hformula] at hb
      rcases (mul_pos_iff.mp hb) with ⟨hd, _⟩ | ⟨_, hneg⟩
      · exact hd
      · exact False.elim ((not_lt_of_ge (le_of_lt hp)) hneg)
  · have hn : φ x b₀ < 0 := lt_of_le_of_ne (le_of_not_gt hp) hbase
    change b.orientation = (if 0 < φ x b₀ then b₀.orientation else -b₀.orientation) ↔ _
    rw [ite_eq_right hp]
    rw [Module.Basis.orientation_eq_neg_iff_det_neg]
    constructor
    · intro hd
      have hprod : b.det b₀ * φ x b < 0 := by rw [← hformula']; exact hn
      rcases (mul_neg_iff.mp hprod) with ⟨hdetpos, hφneg⟩ | ⟨hdet, hφ⟩
      · exact False.elim ((not_lt_of_ge (le_of_lt hdetpos)) hd)
      · exact hφ
    · intro hφ
      have hprod : b.det b₀ * φ x b < 0 := by rw [← hformula']; exact hn
      rcases (mul_neg_iff.mp hprod) with ⟨hdetpos, hφneg⟩ | ⟨hdet, _⟩
      · exact False.elim ((not_lt_of_ge (le_of_lt hφ)) hφneg)
      · exact hdet


/-- A nowhere-vanishing continuous top form determines the manifold orientation on which it is
positive. The orientation is assembled from the locally constant signs of the form in tangent
trivializations, and the final characterization is fibrewise. -/
theorem exists_orientation_of_topForm [IsManifold I 1 M]
    {φ : RoughForm I M ℝ (Module.finrank ℝ E)} (hφ : IsSmoothForm I 0 φ)
    (h0 : ∀ x, φ x ≠ 0) :
    ∃ o : Manifold.Orientation I M (Fin (Module.finrank ℝ E)),
      ∀ (x : M) (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x)),
        b.orientation = Manifold.Orientation.orientationAt o x ↔ 0 < φ x b := by
  let bE := Module.finBasis ℝ E
  let eT : M → Trivialization E (TotalSpace.proj : TangentBundle I M → M) :=
    fun x ↦ trivializationAt E (TangentSpace I) x
  have heT (x : M) : x ∈ (eT x).baseSet := by
    exact FiberBundle.mem_baseSet_trivializationAt' x
  let eA : M → Trivialization (E [⋀^Fin (Module.finrank ℝ E)]→L[ℝ] ℝ)
      (TotalSpace.proj : TotalSpace (E [⋀^Fin (Module.finrank ℝ E)]→L[ℝ] ℝ)
        (fun x ↦ TangentSpace I x [⋀^Fin (Module.finrank ℝ E)]→L[ℝ] ℝ) → M) :=
    fun x ↦ trivializationAt (E [⋀^Fin (Module.finrank ℝ E)]→L[ℝ] ℝ)
      (fun x ↦ TangentSpace I x [⋀^Fin (Module.finrank ℝ E)]→L[ℝ] ℝ) x
  have hbase (a x : M) (hx : x ∈ (eT a).baseSet) : x ∈ (eA a).baseSet := by
    change x ∈ (trivializationAt (E [⋀^Fin (Module.finrank ℝ E)]→L[ℝ] ℝ)
      (fun x ↦ TangentSpace I x [⋀^Fin (Module.finrank ℝ E)]→L[ℝ] ℝ) a).baseSet
    rw [FiberBundle.trivializationAt_continuousAlternatingMap_baseSet,
      TangentBundle.trivializationAt_baseSet]
    exact ⟨hx, FiberBundle.mem_baseSet_trivializationAt' x⟩
  let coord (a x : M) : ℝ := (eA a ⟨x, φ x⟩).2 bE
  have hcoord_cont (a : M) : ContinuousOn (coord a) (eT a).baseSet := by
    let ea := eA a
    have hmap : MapsTo (fun x ↦ TotalSpace.mk'
        (E [⋀^Fin (Module.finrank ℝ E)]→L[ℝ] ℝ) x (φ x))
        (eT a).baseSet ea.source := by
      intro x hx
      rw [ea.mem_source]
      change x ∈ ea.baseSet
      exact hbase a x hx
    have hc : ContinuousOn (fun x ↦ (ea ⟨x, φ x⟩).2) (eT a).baseSet := by
      apply (ea.continuousOn.comp hφ.contMDiff.continuous.continuousOn hmap).snd
    change ContinuousOn (fun x ↦ (ea ⟨x, φ x⟩).2 bE) (eT a).baseSet
    exact (ContinuousAlternatingMap.apply ℝ E ℝ bE).continuous.comp_continuousOn hc
  have hcoord_eq (a x : M) (hx : x ∈ (eT a).baseSet) :
      coord a x = φ x ((eT a).basisAt bE hx :
        Fin (Module.finrank ℝ E) → TangentSpace I x) := by
    simp only [coord, eA, FiberBundle.trivializationAt_continuousAlternatingMap_apply]
    have hy : x ∈ (trivializationAt ℝ (fun _ : M ↦ ℝ) a).baseSet := by
      have h := hbase a x hx
      simpa only [eA, FiberBundle.trivializationAt_continuousAlternatingMap_baseSet,
        TangentBundle.trivializationAt_baseSet] using h.2
    rw [ContinuousAlternatingMap.inCoordinates_eq E ℝ hx hy]
    rw [ContinuousAlternatingMap.compContinuousLinearMap_apply,
      ContinuousLinearMap.compContinuousAlternatingMap_coe]
    congr 1
  have heval_ne (a x : M) (hx : x ∈ (eT a).baseSet) : coord a x ≠ 0 := by
    rw [hcoord_eq a x hx]
    intro h
    apply h0 x
    ext v
    rw [ContinuousAlternatingMap.apply_eq_det_mul (φ x)
      ((eT a).basisAt bE hx) v, h, mul_zero]
    simp
  have hmap_basis (a x : M) (hx : x ∈ (eT a).baseSet) :
      (eT a).mapOrientation (Fin (Module.finrank ℝ E)) hx
        (((eT a).basisAt bE hx).orientation) = bE.orientation := by
    rw [Bundle.Trivialization.mapOrientation_apply, ← Module.Basis.orientation_map]
    let L := Bundle.Trivialization.linearEquivAt ℝ (eT a) x hx
    change ((bE.map L.symm).map L).orientation = bE.orientation
    have hbasis : (bE.map L.symm).map L = bE := by
      ext i
      exact L.apply_symm_apply (bE i)
    rw [hbasis]
  have hmap_sign (a x : M) (hx : x ∈ (eT a).baseSet) :
      (eT a).mapOrientation (Fin (Module.finrank ℝ E)) hx
          (topFormOrientationAt (I := I) φ x) =
        if 0 < coord a x then bE.orientation else -bE.orientation := by
    have hs := topFormOrientationAt_spec (I := I) x (h0 x)
      ((eT a).basisAt bE hx)
    rw [← hcoord_eq a x hx] at hs
    by_cases hp : 0 < coord a x
    · rw [ite_eq_left hp]
      rw [← hs.mpr hp]
      exact hmap_basis a x hx
    · rw [ite_eq_right hp]
      have hs'' : -((eT a).basisAt bE hx).orientation =
          topFormOrientationAt (I := I) φ x := by
        rcases Module.Basis.orientation_eq_or_eq_neg
          ((eT a).basisAt bE hx) (topFormOrientationAt (I := I) φ x) with h | h
        · exact False.elim ((hs.not.mpr hp) h.symm)
        · exact h.symm
      rw [← hs'']
      rw [Bundle.Trivialization.mapOrientation_neg, hmap_basis]
  let o' : ∀ x, _root_.Orientation ℝ (TangentSpace I x) (Fin (Module.finrank ℝ E)) :=
    fun x ↦ topFormOrientationAt (I := I) φ x
  let e : M → Trivialization E (TotalSpace.proj : TangentBundle I M → M) := eT
  have ho : ∀ a, ∀ᶠ x in 𝓝 a, ∀ hx : x ∈ (e a).baseSet,
      (e a).mapOrientation (Fin (Module.finrank ℝ E)) hx (o' x) =
        (e a).mapOrientation (Fin (Module.finrank ℝ E)) (heT a) (o' a) := by
    intro a
    have hca := (hcoord_cont a).continuousAt
      ((eT a).open_baseSet.mem_nhds (heT a))
    have hne := heval_ne a a (heT a)
    by_cases hp : 0 < coord a a
    · filter_upwards [hca.preimage_mem_nhds (isOpen_Ioi.mem_nhds hp)] with x hx hxbase
      change 0 < coord a x at hx
      rw [hmap_sign a x hxbase, hmap_sign a a (heT a), ite_eq_left hx, ite_eq_left hp]
    · have hn : coord a a < 0 := lt_of_le_of_ne (le_of_not_gt hp) hne
      filter_upwards [hca.preimage_mem_nhds (isOpen_Iio.mem_nhds hn)] with x hx hxbase
      change coord a x < 0 at hx
      rw [hmap_sign a x hxbase, hmap_sign a a (heT a), ite_eq_right (not_lt_of_ge (le_of_lt hx)),
        ite_eq_right (not_lt_of_ge (le_of_lt hn))]
  let vo := VectorBundleOrientation.ofEventually (Fintype.card_fin _) o' e heT ho
  refine ⟨Manifold.Orientation.ofVectorBundleOrientation bE.orientation (Fintype.card_fin _) vo, ?_⟩
  intro x b
  rw [Manifold.Orientation.orientationAt_ofVectorBundleOrientation]
  have hvo : vo x = o' x := by
    exact congrFun (VectorBundleOrientation.coe_ofEventually
      (Fintype.card_fin _) o' e heT ho) x
  rw [hvo]
  exact topFormOrientationAt_spec (I := I) x (h0 x) b


end TauCeti
