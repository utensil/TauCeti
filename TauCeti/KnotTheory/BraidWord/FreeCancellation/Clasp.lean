/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.BraidWord.DoubleCrossing.ExternalArcs

/-!
# Crossing-free components after a braid free-cancellation pair

This file records the crossing-free-component part of the closure correspondence for two inverse
crossings prepended on adjacent strands. When both affected positions already meet a crossing,
the inserted pair cannot create a new crossing-free circle; the cases with one or two empty
positions remain separate parts of the free-cancellation correspondence.
-/

public section

namespace TauCeti.BraidWord

open BraidGroup PDCode

variable {n : ℕ}

variable (v : BraidWord n) (i : Fin (n - 1)) (ε : ℤˣ)

private theorem crossinglessPositions_cons_cons
    (ha : v.crossingsAt (strand i) ≠ []) (hb : v.crossingsAt (strandSucc i) ≠ []) :
    Finset.univ.filter (fun p ↦
        crossingsAt (((i, ε) :: (i, -ε) :: v : List _) : BraidWord n) p = []) =
      Finset.univ.filter (fun p ↦ v.crossingsAt p = []) := by
  apply Finset.ext
  intro p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [crossingsAt_cons_cons_same_index]
  by_cases h : p = strand i ∨ p = strandSucc i
  · rcases h with rfl | rfl <;> simp [ha, hb]
  · simp [h]

/-- The inserted inverse pair does not create a crossing-free component when both of its
affected strands already meet a crossing. -/
theorem crossinglessComponentCount_closure_cons_cons
    (ha : v.crossingsAt (strand i) ≠ []) (hb : v.crossingsAt (strandSucc i) ≠ []) :
    (closure ((i, ε) :: (i, -ε) :: v)).crossinglessComponentCount =
      v.closure.crossinglessComponentCount := by
  rw [crossinglessComponentCount_closure, crossinglessComponentCount_closure,
    crossinglessPositions_cons_cons v i ε ha hb]

/-- The inserted inverse pair preserves the crossing-free circles when both affected strands
already meet a crossing. -/
theorem crossinglessComponents_closure_cons_cons
    (ha : v.crossingsAt (strand i) ≠ []) (hb : v.crossingsAt (strandSucc i) ≠ []) :
    (closure ((i, ε) :: (i, -ε) :: v)).crossinglessComponents =
      v.closure.crossinglessComponents := by
  rw [crossinglessComponents_closure, crossinglessComponents_closure,
    crossinglessPositions_cons_cons v i ε ha hb]

end TauCeti.BraidWord
