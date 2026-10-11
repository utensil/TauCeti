/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Star.PL.Basic

/-!
# Piecewise-linear radial star homeomorphisms

A piecewise-linear coordinate description of a homeomorphism between geometric links extends
radially to a piecewise-linear coordinate description of the induced homeomorphism between their
closed stars. The same construction applied to the inverse link homeomorphism supplies the inverse
description. This is the PL compatibility needed when vertex-star charts are assembled from
combinatorial link models.

The radial extension itself is defined in Realization.Star.Homeomorph; this file packages the
two existing local extension results so that callers can use the closed-star homeomorphism and its
inverse without unfolding that construction.

References: Rourke--Sanderson, Introduction to Piecewise-Linear Topology, Chapter 2.
-/

public section

noncomputable section

open Set TauCeti

namespace AbstractSimplicialComplex

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
  {K : AbstractSimplicialComplex ι} {L : AbstractSimplicialComplex κ} {v : ι} {w : κ}

/-- Piecewise-linear ambient formulas for a radial closed-star homeomorphism and its inverse.

The link formulas F and G are required only on the realized links. The returned formulas are
piecewise linear on the corresponding closed stars and agree there with
closedStarHomeomorph hK hL e and its inverse. -/
theorem exists_isPLOn_closedStarHomeomorph
    (hK : Topology.IsInducing (fun x : Realization K => (x.1 : ι → ℝ)))
    (hL : Topology.IsInducing (fun x : Realization L => (x.1 : κ → ℝ)))
    (hKc : IsCompact (geometricLink K v)) (hLc : IsCompact (geometricLink L w))
    (e : geometricLink K v ≃ₜ geometricLink L w)
    (F : (ι → ℝ) → (κ → ℝ))
    (hF : ∀ y : geometricLink K v, F (y.1.1 : ι → ℝ) = (e y).1.1)
    (hFpl : IsPLOn F (range (fun y : geometricLink K v => (y.1.1 : ι → ℝ))))
    (G : (κ → ℝ) → (ι → ℝ))
    (hG : ∀ y : geometricLink L w, G (y.1.1 : κ → ℝ) = (e.symm y).1.1)
    (hGpl : IsPLOn G (range (fun y : geometricLink L w => (y.1.1 : κ → ℝ)))) :
    ∃ F' : (ι → ℝ) → (κ → ℝ), ∃ G' : (κ → ℝ) → (ι → ℝ),
      IsPLOn F'
          (range (fun x : closedStarRealization K {v} => (x.1.1 : ι → ℝ))) ∧
        IsPLOn G'
          (range (fun x : closedStarRealization L {w} => (x.1.1 : κ → ℝ))) ∧
        (∀ x : closedStarRealization K {v},
          F' (x.1.1 : ι → ℝ) = (closedStarHomeomorph hK hL e x).1.1) ∧
        (∀ x : closedStarRealization L {w},
          G' (x.1.1 : κ → ℝ) = ((closedStarHomeomorph hK hL e).symm x).1.1) ∧
        (∀ x : closedStarRealization K {v},
          G' (F' (x.1.1 : ι → ℝ)) = (x.1.1 : ι → ℝ)) ∧
        (∀ x : closedStarRealization L {w},
          F' (G' (x.1.1 : κ → ℝ)) = (x.1.1 : κ → ℝ)) := by
  obtain ⟨F', hF'pl, hF'eq⟩ := exists_isPLOn_closedStarMap hKc e F hF hFpl
  obtain ⟨G', hG'pl, hG'eq⟩ := exists_isPLOn_closedStarMap hLc e.symm G hG hGpl
  refine ⟨F', G', hF'pl, hG'pl, ?_, ?_⟩
  · intro x
    rw [closedStarHomeomorph_apply]
    exact hF'eq x
  · constructor
    · intro x
      rw [closedStarHomeomorph_symm_apply]
      exact hG'eq x
    · constructor
      · intro x
        have hforward := hF'eq x
        calc
          G' (F' (x.1.1 : ι → ℝ)) =
              G' ((closedStarMap e x).1.1 : κ → ℝ) := by rw [hforward]
          _ = (closedStarMap e.symm (closedStarMap e x)).1.1 := hG'eq _
          _ = (x.1.1 : ι → ℝ) := by
            rw [closedStarMap_comp]
            have hid : (e.symm ∘ e : geometricLink K v → geometricLink K v) = id := by
              funext y
              exact e.symm_apply_apply y
            rw [hid, closedStarMap_id]
      · intro x
        have hbackward := hG'eq x
        calc
          F' (G' (x.1.1 : κ → ℝ)) =
              F' ((closedStarMap e.symm x).1.1 : ι → ℝ) := by rw [hbackward]
          _ = (closedStarMap e (closedStarMap e.symm x)).1.1 := hF'eq _
          _ = (x.1.1 : κ → ℝ) := by
            rw [closedStarMap_comp]
            have hid : (e ∘ e.symm : geometricLink L w → geometricLink L w) = id := by
              funext y
              exact e.apply_symm_apply y
            rw [hid, closedStarMap_id]

end AbstractSimplicialComplex
