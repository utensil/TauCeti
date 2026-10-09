/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.BraidWord.FreeCancellation.Basic
public import TauCeti.KnotTheory.BraidWord.DoubleCrossing.Basic

/-!
# Crossing data for free cancellation in braid closures

An inverse pair inserted into a braid word contributes a Reidemeister-II clasp to its closure.
This file records the local crossing data needed by the eventual diagrammatic
identification: old crossings retain their signs, and the two new crossings have opposite signs
and opposite over-pair indicators.  The existing `DoubleCrossing` API supplies the two internal
arcs; the remaining closure theorem must match the external arcs with a `PDCode.insertClasp` and
prove its face condition.

The context-indexed statements use the insertion point as the crossing index, so they apply to
all `FreeCancelStep` witnesses.  The inserted crossing names are consecutive, and the old crossings
are compared at their shifted indices.  Matching the numbering of `PDCode.insertClasp` still
requires crossing relabeling.
-/

public section
namespace TauCeti
namespace BraidWord

open BraidGroup PDCode

variable {n : ℕ}

/-- The first crossing of an inverse pair inserted in a word context has the sign of its letter. -/
theorem crossingSign_closure_insert_freeCancel_first (u v : BraidWord n) (i : Fin (n - 1))
    (ε : ℤˣ) :
    (closure (u ++ [(i, ε), (i, -ε)] ++ v)).crossingSign
        ⟨u.length, by simp [List.length_append]⟩ = ε := by
  rw [crossingSign_closure]
  simp [List.getElem_append_right]

/-- The second crossing of an inverse pair inserted in a word context has the opposite sign. -/
theorem crossingSign_closure_insert_freeCancel_second (u v : BraidWord n) (i : Fin (n - 1))
    (ε : ℤˣ) :
    (closure (u ++ [(i, ε), (i, -ε)] ++ v)).crossingSign
        ⟨u.length + 1, by simp [List.length_append]⟩ = -ε := by
  rw [crossingSign_closure]
  simp [List.getElem_append_right]

/-- The two crossings inserted by free cancellation have opposite over-pair indicators. -/
theorem overPair_closure_insert_freeCancel_second_eq_not_first
    (u v : BraidWord n) (i : Fin (n - 1)) (ε : ℤˣ) :
    (closure (u ++ [(i, ε), (i, -ε)] ++ v)).overPair
        ⟨u.length + 1, by simp [List.length_append]⟩ =
      !(closure (u ++ [(i, ε), (i, -ε)] ++ v)).overPair
        ⟨u.length, by simp [List.length_append]⟩ := by
  rw [overPair_closure, overPair_closure]
  rcases Int.units_eq_one_or ε with rfl | rfl <;> simp [List.getElem_append_right]

/-- Crossings from the left context retain their signs after an inverse pair is inserted. -/
theorem crossingSign_closure_insert_freeCancel_left (u v : BraidWord n) (i : Fin (n - 1))
    (ε : ℤˣ) (j : Fin u.length) :
    (closure (u ++ [(i, ε), (i, -ε)] ++ v)).crossingSign
        ⟨j, by simp [List.length_append]; omega⟩ =
      (closure (u ++ v)).crossingSign ⟨j, by simp [List.length_append]; omega⟩ := by
  rw [crossingSign_closure, crossingSign_closure]
  simp [List.getElem_append_left]

/-- Crossings from the right context retain their signs after an inverse pair is inserted. -/
theorem crossingSign_closure_insert_freeCancel_right (u v : BraidWord n) (i : Fin (n - 1))
    (ε : ℤˣ) (j : Fin v.length) :
    (closure (u ++ [(i, ε), (i, -ε)] ++ v)).crossingSign
        ⟨u.length + 2 + j, by simp [List.length_append]; omega⟩ =
      (closure (u ++ v)).crossingSign
        ⟨u.length + j, by simp [List.length_append]⟩ := by
  rw [crossingSign_closure, crossingSign_closure]
  rw [List.getElem_append_right (by simp), List.getElem_append_right (by simp)]
  simp

/-- The over-pair indicator of a left-context crossing is unchanged by insertion. -/
theorem overPair_closure_insert_freeCancel_left (u v : BraidWord n) (i : Fin (n - 1))
    (ε : ℤˣ) (j : Fin u.length) :
    (closure (u ++ [(i, ε), (i, -ε)] ++ v)).overPair
        ⟨j, by simp [List.length_append]; omega⟩ =
      (closure (u ++ v)).overPair ⟨j, by simp [List.length_append]; omega⟩ := by
  rw [overPair_closure, overPair_closure]
  simp [List.getElem_append_left]

/-- The over-pair indicator of a right-context crossing is unchanged by insertion. -/
theorem overPair_closure_insert_freeCancel_right (u v : BraidWord n) (i : Fin (n - 1))
    (ε : ℤˣ) (j : Fin v.length) :
    (closure (u ++ [(i, ε), (i, -ε)] ++ v)).overPair
        ⟨u.length + 2 + j, by simp [List.length_append]; omega⟩ =
      (closure (u ++ v)).overPair
        ⟨u.length + j, by simp [List.length_append]⟩ := by
  rw [overPair_closure, overPair_closure]
  rw [List.getElem_append_right (by simp), List.getElem_append_right (by simp)]
  simp

end BraidWord
end TauCeti
