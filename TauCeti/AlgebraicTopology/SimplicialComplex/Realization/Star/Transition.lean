/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Star.PL

/-!
# Piecewise-linear compositions of radial star maps

The PL extension theorem for a radial map is local to one closed star.  Vertex-star atlas
transitions use two such extensions in succession, so the target set of the first formula must be
tracked explicitly when the PL composition lemma is applied.  This file packages that bookkeeping
and identifies the resulting composition with the radial extension of the composite link map.

This is the composition step used by the `realize_combinatorialManifold_isPL` construction in the
GeometricTopology roadmap.  It does not assert that a link map is PL; callers provide the two
ambient link formulas and their `IsPLOn` proofs.

Reference: Rourke--Sanderson, *Introduction to Piecewise-Linear Topology*, Chapters 1--2.
-/

public section

noncomputable section

open Set TauCeti

namespace AbstractSimplicialComplex

variable {ι κ ν : Type*} [DecidableEq ι] [DecidableEq κ] [DecidableEq ν]
  {K : AbstractSimplicialComplex ι} {L : AbstractSimplicialComplex κ}
  {N : AbstractSimplicialComplex ν} {v : ι} {w : κ} {u : ν}

/-- Two piecewise-linear radial closed-star maps compose piecewise linearly.

The returned ambient formula is piecewise linear on the source closed star and agrees there with
the radial extension of `g ∘ f`.  The compactness assumptions are exactly those required by
`exists_isPLOn_closedStarMap` for the two successive extensions; no compactness of the ambient
complexes is needed.
-/
theorem exists_isPLOn_closedStarMap_comp
    (hK : IsCompact (geometricLink K v))
    (hL : IsCompact (geometricLink L w))
    (f : geometricLink K v → geometricLink L w)
    (g : geometricLink L w → geometricLink N u)
    (F : (ι → ℝ) → (κ → ℝ))
    (hF : ∀ y : geometricLink K v, F (y.1.1 : ι → ℝ) = (f y).1.1)
    (hFpl : IsPLOn F (range (fun y : geometricLink K v => (y.1.1 : ι → ℝ))))
    (G : (κ → ℝ) → (ν → ℝ))
    (hG : ∀ y : geometricLink L w, G (y.1.1 : κ → ℝ) = (g y).1.1)
    (hGpl : IsPLOn G (range (fun y : geometricLink L w => (y.1.1 : κ → ℝ)))) :
    ∃ H : (ι → ℝ) → (ν → ℝ),
      IsPLOn H (range (fun x : closedStarRealization K {v} => (x.1.1 : ι → ℝ))) ∧
        ∀ x : closedStarRealization K {v},
          H (x.1.1 : ι → ℝ) = (closedStarMap (g ∘ f) x).1.1 := by
  obtain ⟨F', hF'pl, hF'eq⟩ := exists_isPLOn_closedStarMap hK f F hF hFpl
  obtain ⟨G', hG'pl, hG'eq⟩ := exists_isPLOn_closedStarMap hL g G hG hGpl
  let S : Set (ι → ℝ) := range (fun x : closedStarRealization K {v} => (x.1.1 : ι → ℝ))
  let T : Set (κ → ℝ) := range (fun y : closedStarRealization L {w} => (y.1.1 : κ → ℝ))
  have hST : S ⊆ F' ⁻¹' T := by
    rintro _ ⟨x, rfl⟩
    rw [Set.mem_preimage, hF'eq x]
    exact Set.mem_range.mpr ⟨closedStarMap f x, rfl⟩
  refine ⟨G' ∘ F', hG'pl.comp hF'pl hST, ?_⟩
  intro x
  rw [Function.comp_apply, hF'eq x, hG'eq]
  rw [closedStarMap_comp]

end AbstractSimplicialComplex
