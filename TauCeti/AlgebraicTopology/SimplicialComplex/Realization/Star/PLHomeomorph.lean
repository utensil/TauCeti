/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Star.PL

/-!
# Two-sided PL coordinates for radial star homeomorphisms

The radial extension of a homeomorphism between geometric links is the local model used to
compare vertex charts in a combinatorial manifold. `Realization.Star.PL` constructs a PL ambient
formula for one direction of this extension. This file packages that result with the corresponding
formula for the inverse, so a chart transition carries the two-sided PL data it needs in one
witness.

The theorem is deliberately stated in terms of coordinate formulas on the realized closed stars.
The global atlas argument, and the proof that the link homeomorphism itself is PL, are separate
parts of the combinatorial-manifold to PL-manifold reconciliation.
-/

public section

noncomputable section

open Set TauCeti

namespace AbstractSimplicialComplex

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
  {K : AbstractSimplicialComplex ι} {L : AbstractSimplicialComplex κ} {v : ι} {w : κ}

/-- A PL coordinate formula for a link homeomorphism and one for its inverse extend simultaneously
to the two directions of the radial homeomorphism of the corresponding closed vertex stars.

`hF` and `hFsymm` identify the ambient formulas with the coordinate maps on the links. The two
resulting formulas are returned with their PL-on-star proofs and their pointwise values on the
actual star maps. This is the local two-sided witness used by PL star-chart transitions. -/
theorem exists_isPLOn_closedStarHomeomorph
    (hK : Topology.IsInducing (fun x : Realization K => (x.1 : ι → ℝ)))
    (hL : Topology.IsInducing (fun x : Realization L => (x.1 : κ → ℝ)))
    (hcK : IsCompact (geometricLink K v)) (hcL : IsCompact (geometricLink L w))
    (e : geometricLink K v ≃ₜ geometricLink L w)
    (F : (ι → ℝ) → (κ → ℝ))
    (hF : ∀ y : geometricLink K v, F (y.1.1 : ι → ℝ) = (e y).1.1)
    (hf : IsPLOn F (range (fun y : geometricLink K v => (y.1.1 : ι → ℝ))))
    (Fsymm : (κ → ℝ) → (ι → ℝ))
    (hFsymm : ∀ y : geometricLink L w, Fsymm (y.1.1 : κ → ℝ) = (e.symm y).1.1)
    (hfsymm : IsPLOn Fsymm (range (fun y : geometricLink L w => (y.1.1 : κ → ℝ)))) :
    ∃ G : (ι → ℝ) → (κ → ℝ), ∃ Gsymm : (κ → ℝ) → (ι → ℝ),
      IsPLOn G (range (fun x : closedStarRealization K {v} => (x.1.1 : ι → ℝ))) ∧
        IsPLOn Gsymm (range (fun x : closedStarRealization L {w} => (x.1.1 : κ → ℝ))) ∧
        (∀ x : closedStarRealization K {v},
          G (x.1.1 : ι → ℝ) = (closedStarHomeomorph hK hL e x).1.1) ∧
        (∀ y : closedStarRealization L {w},
          Gsymm (y.1.1 : κ → ℝ) = ((closedStarHomeomorph hK hL e).symm y).1.1) ∧
        (∀ x : closedStarRealization K {v},
          Gsymm (G (x.1.1 : ι → ℝ)) = x.1.1) ∧
        (∀ y : closedStarRealization L {w},
          G (Gsymm (y.1.1 : κ → ℝ)) = y.1.1) := by
  obtain ⟨G, hG, hG_apply⟩ := exists_isPLOn_closedStarMap hcK e F hF hf
  obtain ⟨Gsymm, hGsymm, hGsymm_apply⟩ :=
    exists_isPLOn_closedStarMap hcL e.symm Fsymm hFsymm hfsymm
  refine ⟨G, Gsymm, hG, hGsymm, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    simpa only [closedStarHomeomorph_apply] using hG_apply x
  · intro y
    simpa only [closedStarHomeomorph_symm_apply] using hGsymm_apply y
  · intro x
    calc
      Gsymm (G (x.1.1 : ι → ℝ)) =
          Gsymm ((closedStarHomeomorph hK hL e x).1.1) :=
        congrArg Gsymm (by simpa only [closedStarHomeomorph_apply] using hG_apply x)
      _ = ((closedStarHomeomorph hK hL e).symm (closedStarHomeomorph hK hL e x)).1.1 :=
        by simpa only [closedStarHomeomorph_symm_apply] using hGsymm_apply _
      _ = x.1.1 := by simp
  · intro y
    calc
      G (Gsymm (y.1.1 : κ → ℝ)) =
          G ((closedStarHomeomorph hK hL e).symm y).1.1 :=
        congrArg G (by simpa only [closedStarHomeomorph_symm_apply] using hGsymm_apply y)
      _ = (closedStarHomeomorph hK hL e ((closedStarHomeomorph hK hL e).symm y)).1.1 :=
        by simpa only [closedStarHomeomorph_apply] using hG_apply _
      _ = y.1.1 := by simp

end AbstractSimplicialComplex
