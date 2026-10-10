/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Stellar.Geometry
public import TauCeti.Topology.PL.FiniteInf
public import TauCeti.Topology.PL.Product

/-!
# Piecewise-linear inverses for stellar subdivisions

A stellar subdivision places a new vertex at the barycenter of a face.  Its realization map is
linear in barycentric coordinates, while the inverse transfers the least coordinate on the
starred face to the new vertex.  This file records that inverse and its piecewise-affine
regularity.  These formulas are the local PL identifications used when transporting
combinatorial links to standard simplices.

The inverse is defined on the whole coordinate space by the minimum formula; on the
subdivided polyhedron the minimum is the coordinate that vanishes on the containing face, so
the formula is the inverse of the barycentric map.

Reference: Rourke--Sanderson, *Introduction to Piecewise-Linear Topology*, Chapter 2.
-/

public section

noncomputable section

open Set TauCeti

namespace Finset

variable {ι : Type*} [DecidableEq ι]

/-- The minimum-coordinate inverse to the barycentric map of a stellar subdivision. -/
def stellarSubdivisionInverse (σ : Finset ι) (v : ι) (hσ : σ.Nonempty) (x : ι → ℝ) : ι → ℝ :=
  x + σ.inf' hσ (fun i => x i) •
    ((σ.card : ℝ) • Pi.single v 1 - ∑ i ∈ σ, Pi.single i 1)

@[simp]
theorem stellarSubdivisionInverse_apply (σ : Finset ι) (v : ι) (hσ : σ.Nonempty)
    (x : ι → ℝ) (i : ι) :
    stellarSubdivisionInverse σ v hσ x i =
      x i + σ.inf' hσ (fun j => x j) *
        ((if i = v then (σ.card : ℝ) else 0) - if i ∈ σ then 1 else 0) := by
  by_cases hiv : i = v <;> simp [stellarSubdivisionInverse, Pi.single_apply, hiv]

/-- The minimum-coordinate inverse is piecewise affine on the whole coordinate space. -/
theorem isPLOn_stellarSubdivisionInverse (σ : Finset ι) (v : ι) (hσ : σ.Nonempty) :
    IsPLOn (stellarSubdivisionInverse σ v hσ) (Set.univ : Set (ι → ℝ)) := by
  let m : (ι → ℝ) → ℝ := fun x => σ.inf' hσ (fun i => x i)
  have hm : IsPLOn m (Set.univ : Set (ι → ℝ)) :=
    σ.isPLOn_infAffine hσ (fun i => (ContinuousLinearMap.proj i).toContinuousAffineMap)
  let c : ι → ℝ := (σ.card : ℝ) • Pi.single v 1 - ∑ i ∈ σ, Pi.single i 1
  let A : ((ι → ℝ) × ℝ) →L[ℝ] (ι → ℝ) :=
    ContinuousLinearMap.fst ℝ (ι → ℝ) ℝ +
      (ContinuousLinearMap.snd ℝ (ι → ℝ) ℝ).smulRight c
  have hpair : IsPLOn (fun x : ι → ℝ => (x, m x)) (Set.univ : Set (ι → ℝ)) :=
    (isPLOn_id _).prodMk hm
  have hA : IsPLOn (A : (ι → ℝ) × ℝ → ι → ℝ) (Set.univ : Set ((ι → ℝ) × ℝ)) :=
    isPLOn_continuousAffineMap A.toContinuousAffineMap _
  have hcomp := hA.comp hpair (by simp)
  refine hcomp.congr ?_
  intro x hx
  simp only [Function.comp_apply, A, c, m, stellarSubdivisionInverse]
  rfl

end Finset

namespace PreAbstractSimplicialComplex

open Finset

variable {ι : Type*} [DecidableEq ι] {K : PreAbstractSimplicialComplex ι}
  {σ : Finset ι} {v : ι}

/-- The minimum-coordinate inverse recovers barycentric coordinates on every simplex of a
stellar subdivision. -/
theorem stellarSubdivisionInverse_stellarSubdivisionLinearMap
    (hσ : σ ∈ K) (hv : ({v} : Finset ι) ∉ K) {x : ι →₀ ℝ}
    (hτ : x.support ∈ stellarSubdivision K σ v) (hx : ∀ i, 0 ≤ x i) :
    (fun i => Finset.stellarSubdivisionInverse σ v (K.isRelLowerSet_faces hσ).1
      (fun j => Finset.stellarSubdivisionLinearMap σ v x j) i) = x := by
  have hvσ : v ∉ σ := by
    intro hvσ
    exact hv ((K.isRelLowerSet_faces hσ).2 (singleton_subset_iff.mpr hvσ) (by simp))
  have hσne : σ.Nonempty := (K.isRelLowerSet_faces hσ).1
  obtain ⟨a, haσ, haτ⟩ := exists_notMem_of_mem_stellarSubdivision hvσ hτ
  have hxa : x a = 0 := by
    by_contra hxa
    exact haτ ((Finsupp.mem_support_iff).2 hxa)
  have hcard : (σ.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr hσne)
  have hmin :
      σ.inf' hσne (fun i => Finset.stellarSubdivisionLinearMap σ v x i) = x v / σ.card := by
    apply le_antisymm
    · calc
        σ.inf' hσne (fun i => Finset.stellarSubdivisionLinearMap σ v x i) ≤
            Finset.stellarSubdivisionLinearMap σ v x a := Finset.inf'_le _ haσ
        _ = x v / σ.card := by
          have hav : a ≠ v := by
            intro hav
            exact hvσ (hav ▸ haσ)
          rw [Finset.stellarSubdivisionLinearMap_apply]
          simp [hxa, hav, haσ, div_eq_mul_inv]
    · apply Finset.le_inf' hσne
      intro i hi
      have hiv : i ≠ v := by
        intro hiv
        exact hvσ (hiv ▸ hi)
      rw [Finset.stellarSubdivisionLinearMap_apply]
      simp only [hiv, hi, ite_false, ite_true, sub_zero, div_eq_mul_inv]
      exact le_add_of_nonneg_left (hx i)
  funext i
  rw [Finset.stellarSubdivisionInverse_apply, hmin,
    Finset.stellarSubdivisionLinearMap_apply]
  by_cases hiv : i = v
  · simp [hiv, hvσ]
    field_simp [hcard]
  by_cases hiσ : i ∈ σ
  · simp [hiv, hiσ]
    field_simp [hcard]
    ring
  · simp [hiv, hiσ]

end PreAbstractSimplicialComplex
