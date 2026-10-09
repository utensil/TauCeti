/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.BraidWord.CrossinglessComponents
public import TauCeti.KnotTheory.PDCode.Oriented.Reidemeister.Two.Circles

/-!
# Crossing-free components in the two-circle free-cancellation case

When both strands at an inverse braid pair are crossing-free, inserting the pair changes the
crossing-free component multiset by removing the two affected circles.  Adjoining the closed
two-circle clasp changes the same multiset in exactly the same way.  These equalities are the
component-bookkeeping prerequisite for the Reidemeister-II identification of this branch.

The full diagram equality still requires the separate half-edge, arc, over-strand, and orientation
comparison for the relabelled clasp.
-/

public section

namespace TauCeti.BraidWord

open BraidGroup

variable {n : ℕ}

/-- In the two-circle branch, adding back the two crossing-free circles consumed by the inverse
pair recovers the old closure's crossing-free component multiset.  The signs of the pair are
fixed to be inverse, while both affected positions are assumed crossing-free. -/
theorem crossinglessComponents_closure_cons_cons_freeCancel_twoCircles
    (v : BraidWord n) (i : Fin (n - 1)) (ε : ℤˣ)
    (hp : v.crossingsAt (strand i) = []) (hq : v.crossingsAt (strandSucc i) = []) :
    (closure ((i, ε) :: (i, -ε) :: v)).crossinglessComponents +
        {true} + {true} = v.closure.crossinglessComponents := by
  have h := crossinglessComponents_closure_insert_pair ([] : BraidWord n) v i ε (-ε)
  simpa [crossinglessComponents_closure, crossingsAt_cons_cons_same_index, hp, hq] using h

/-- The crossing-free component multiset of the inverse-pair closure, after restoring its two
consumed circles, is the multiset supplied by the corresponding closed clasp. -/
theorem crossinglessComponents_closure_cons_cons_freeCancel_twoCircles_eq_clasp
    (v : BraidWord n) (i : Fin (n - 1)) (ε : ℤˣ)
    (hp : v.crossingsAt (strand i) = []) (hq : v.crossingsAt (strandSucc i) = []) :
    (closure ((i, ε) :: (i, -ε) :: v)).crossinglessComponents + {true} + {true} =
      (v.closure.adjoinTwoCircleClasp true true (decide (ε = -1))).crossinglessComponents := by
  rw [OrientedPDCode.crossinglessComponents_adjoinTwoCircleClasp]
  exact crossinglessComponents_closure_cons_cons_freeCancel_twoCircles v i ε hp hq

end TauCeti.BraidWord
