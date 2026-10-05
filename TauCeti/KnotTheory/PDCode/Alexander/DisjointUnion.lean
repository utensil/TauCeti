/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.Alexander.Basic
public import TauCeti.KnotTheory.PDCode.Oriented.DisjointUnion

/-!
# Alexander coordinates of a disjoint union

The Alexander presentation of a disjoint union is assembled from the two presentations without
mixing their crossing data.  This file records the coefficient formulas used when transporting
Alexander relations across the canonical crossing and half-edge reindexings.  They are the local
coordinate API for the planned direct-sum equivalence of Alexander modules.
-/

public section

namespace TauCeti.OrientedPDCode

open PDCode

variable {n m : ℕ} (D : OrientedPDCode n) (E : OrientedPDCode m)

/-- The over-strand indicator of a crossing in the first summand is unchanged by disjoint union. -/
@[simp] theorem isOver_disjointUnion_castAdd (i : Fin n) (slot : Fin 4) :
    (D.toPDCode.disjointUnion E.toPDCode).isOver (Fin.castAdd m i) slot =
      D.toPDCode.isOver i slot := by
  simp [PDCode.isOver_def]

/-- The over-strand indicator of a crossing in the second summand is unchanged by disjoint union. -/
@[simp] theorem isOver_disjointUnion_natAdd (i : Fin m) (slot : Fin 4) :
    (D.toPDCode.disjointUnion E.toPDCode).isOver (Fin.natAdd n i) slot =
      E.toPDCode.isOver i slot := by
  simp [PDCode.isOver_def]

/-- The Alexander weights of the first summand are unchanged by disjoint union. -/
@[simp] theorem alexanderWeight_disjointUnion_castAdd (i : Fin n) (slot : Fin 4) :
    (D.disjointUnion E).alexanderWeight (Fin.castAdd m i) slot = D.alexanderWeight i slot := by
  rw [alexanderWeight_def, alexanderWeight_def]
  have hOver :
      (D.disjointUnion E).isOver (Fin.castAdd m i) slot = D.isOver i slot := by
    simpa only [toPDCode_disjointUnion] using isOver_disjointUnion_castAdd D E i slot
  have hOrientation :
      (D.disjointUnion E).orientation
          ((D.disjointUnion E).crossing (Fin.castAdd m i) slot) =
        D.orientation (D.crossing i slot) := by
    simp only [toPDCode_disjointUnion, PDCode.crossing_apply, PDCode.disjointUnion_halfEdge,
      Equiv.permCongr_apply, disjointUnionHalfEdgeEquiv_symm_crossingSlot_castAdd,
      Equiv.sumCongr_apply, Sum.map_inl, orientation_disjointUnion_inl]
  rw [hOver, hOrientation, crossingSign_disjointUnion_castAdd]

/-- The Alexander weights of the second summand are unchanged by disjoint union. -/
@[simp] theorem alexanderWeight_disjointUnion_natAdd (i : Fin m) (slot : Fin 4) :
    (D.disjointUnion E).alexanderWeight (Fin.natAdd n i) slot = E.alexanderWeight i slot := by
  rw [alexanderWeight_def, alexanderWeight_def]
  have hOver :
      (D.disjointUnion E).isOver (Fin.natAdd n i) slot = E.isOver i slot := by
    simpa only [toPDCode_disjointUnion] using isOver_disjointUnion_natAdd D E i slot
  have hOrientation :
      (D.disjointUnion E).orientation
          ((D.disjointUnion E).crossing (Fin.natAdd n i) slot) =
        E.orientation (E.crossing i slot) := by
    simp only [toPDCode_disjointUnion, PDCode.crossing_apply, PDCode.disjointUnion_halfEdge,
      Equiv.permCongr_apply, disjointUnionHalfEdgeEquiv_symm_crossingSlot_natAdd,
      Equiv.sumCongr_apply, Sum.map_inr, orientation_disjointUnion_inr]
  rw [hOver, hOrientation, crossingSign_disjointUnion_natAdd]

end TauCeti.OrientedPDCode
