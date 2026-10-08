/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.BraidWord.FreeCancellation.Basic

/-!
# Crossing-free components after a free cancellation

The closure of a braid word has one crossing-free circle for each strand position which never
meets a crossing.  Prepending two letters with the same generator removes precisely the
crossing-free circles on the two affected positions.  These formulas are the component
bookkeeping needed when the resulting two-crossing clasp is compared with `PDCode.insertClasp`.

## Main declarations

* `TauCeti.BraidWord.crossinglessComponents_cons_cons_same_index`: the exact multiset of
  crossing-free orientations after inserting two letters.
* `TauCeti.BraidWord.crossinglessComponentCount_cons_cons_same_index`: its cardinality.

The formula allows either affected position to have been crossing-free in the original word;
the two positions are distinct by the braid-word indexing convention.

## References

* J. Birman, *Braids, Links, and Mapping Class Groups*, Annals of Mathematics Studies 82
  (1974), Chapter 2.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 1.
-/

public section

namespace TauCeti
namespace BraidWord

open BraidGroup PDCode

variable {n : ℕ}

/-- The crossing-free circles after adding two letters are exactly those old strand positions
which are not either affected position and carried no crossing before the insertion. -/
theorem crossinglessComponents_cons_cons_same_index (v : BraidWord n) (i : Fin (n - 1))
    (ε η : ℤˣ) :
    (closure ((i, ε) :: (i, η) :: v)).crossinglessComponents =
      Multiset.replicate
        (Finset.univ.filter fun p : Fin n =>
          p ≠ strand i ∧ p ≠ strandSucc i ∧ v.crossingsAt p = []).card true := by
  rw [crossinglessComponents_closure]
  apply congrArg (fun k => Multiset.replicate k true)
  congr 1
  ext p
  simp [crossingsAt_cons_cons_same_index, and_assoc]

/-- The number of crossing-free circles after adding two letters is the number of old
crossing-free strand positions away from the two affected positions. -/
theorem crossinglessComponentCount_cons_cons_same_index (v : BraidWord n) (i : Fin (n - 1))
    (ε η : ℤˣ) :
    (closure ((i, ε) :: (i, η) :: v)).crossinglessComponentCount =
      (Finset.univ.filter fun p : Fin n =>
        p ≠ strand i ∧ p ≠ strandSucc i ∧ v.crossingsAt p = []).card := by
  rw [← (closure ((i, ε) :: (i, η) :: v)).card_crossinglessComponents,
    crossinglessComponents_cons_cons_same_index]
  simp

end BraidWord
end TauCeti
