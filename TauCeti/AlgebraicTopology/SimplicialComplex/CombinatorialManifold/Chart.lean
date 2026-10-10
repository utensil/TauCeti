/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Star.Ball
public import Mathlib.Topology.OpenPartialHomeomorph.Composition

/-!
# Ambient charts for open vertex stars

A compact closed vertex star with a spherical link has an open-star model in an open Euclidean
ball. This file turns that model into an `OpenPartialHomeomorph` on the ambient realization. The
ambient source and target sets are exposed explicitly so that a future PL atlas can use these
charts directly.
-/

public section
noncomputable section

open Set Filter Topology NormedSpace Metric TauCeti.SetLike

namespace AbstractSimplicialComplex

variable {ι E : Type*} [DecidableEq ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : AbstractSimplicialComplex ι} {v : ι}

private instance openStarNonempty : Nonempty (openStarRealization K v) := by
  exact ⟨⟨vertex K v, by
    rw [mem_openStarRealization]
    simp [vertex_val]⟩⟩

private instance ballNonempty : Nonempty (Metric.ball (0 : E) 1) := by
  exact ⟨⟨0, by rw [mem_ball]; simp⟩⟩

/-- The ambient local chart obtained from a compact closed star and a spherical link model.

The chart is defined on the open vertex star and maps it into the ambient Euclidean space. Its
restriction to the open star is the existing `openStarHomeomorphBall`; the subtype embedding of
the open ball supplies the ambient target set.
-/
noncomputable def openStarChart
    (hK : IsCompact (closedStarRealization K {v}))
    (e : geometricLink K v ≃ₜ Metric.sphere (0 : E) 1) :
    OpenPartialHomeomorph (Realization K) E :=
  ((Topology.IsOpenEmbedding.toOpenPartialHomeomorph
      (fun y : openStarRealization K v => (y : Realization K))
      (K.isOpen_openStarRealization v).isOpenEmbedding_subtypeVal).symm).trans
    ((openStarHomeomorphBall hK e).transOpenPartialHomeomorph
      (Metric.isOpen_ball.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph _))

/-- The source of `openStarChart` is the open star of the chosen vertex. -/
@[simp]
theorem openStarChart_source
    (hK : IsCompact (closedStarRealization K {v}))
    (e : geometricLink K v ≃ₜ Metric.sphere (0 : E) 1) :
    (openStarChart hK e).source = K.openStarRealization v := by
  simp only [openStarChart, OpenPartialHomeomorph.trans_toPartialEquiv,
    OpenPartialHomeomorph.symm_toPartialEquiv, PartialEquiv.trans_source, PartialEquiv.symm_source,
    IsOpenEmbedding.toOpenPartialHomeomorph_target, Subtype.range_coe_subtype,
    mem_openStarRealization,
    PartialHomeomorph.coe_toPartialEquiv_symm, OpenPartialHomeomorph.coe_toPartialHomeomorph_symm,
    Homeomorph.transOpenPartialHomeomorph_source, IsOpenEmbedding.toOpenPartialHomeomorph_source,
    preimage_univ, inter_univ]
  ext x
  simp only [mem_ofPred_eq, mem_openStarRealization]

/-- The target of `openStarChart` is the open unit ball in the ambient space. -/
@[simp]
theorem openStarChart_target
    (hK : IsCompact (closedStarRealization K {v}))
    (e : geometricLink K v ≃ₜ Metric.sphere (0 : E) 1) :
    (openStarChart hK e).target = Metric.ball (0 : E) 1 := by
  simp only [openStarChart, OpenPartialHomeomorph.trans_toPartialEquiv,
    OpenPartialHomeomorph.symm_toPartialEquiv, PartialEquiv.trans_target,
    Homeomorph.transOpenPartialHomeomorph_target,
    IsOpenEmbedding.toOpenPartialHomeomorph_target,
    Subtype.range_coe_subtype, mem_ball, dist_zero_right, PartialHomeomorph.coe_toPartialEquiv_symm,
    OpenPartialHomeomorph.coe_toPartialHomeomorph_symm,
    Homeomorph.transOpenPartialHomeomorph_symm_apply, PartialEquiv.symm_target,
    IsOpenEmbedding.toOpenPartialHomeomorph_source, preimage_univ, inter_univ]
  ext x
  simp only [mem_ofPred_eq, mem_ball, dist_zero_right]

/-- On its source, `openStarChart` agrees with the open-star ball model. -/
theorem openStarChart_apply
    (hK : IsCompact (closedStarRealization K {v}))
    (e : geometricLink K v ≃ₜ Metric.sphere (0 : E) 1)
    {x : Realization K} (hx : x ∈ K.openStarRealization v) :
    openStarChart hK e x =
      (openStarHomeomorphBall hK e ⟨x, hx⟩ : Metric.ball (0 : E) 1) := by
  have hs : ((Topology.IsOpenEmbedding.toOpenPartialHomeomorph
      (fun y : openStarRealization K v => (y : Realization K))
      (K.isOpen_openStarRealization v).isOpenEmbedding_subtypeVal).symm x) = ⟨x, hx⟩ := by
    apply Subtype.ext
    exact (Topology.IsOpenEmbedding.toOpenPartialHomeomorph
      (fun y : openStarRealization K v => (y : Realization K))
      (K.isOpen_openStarRealization v).isOpenEmbedding_subtypeVal).right_inv (by
        rw [Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target]
        exact ⟨⟨x, hx⟩, rfl⟩)
  simp only [openStarChart, OpenPartialHomeomorph.coe_trans,
    Homeomorph.transOpenPartialHomeomorph_apply, Function.comp_apply]
  rw [hs]
  rfl

end AbstractSimplicialComplex
