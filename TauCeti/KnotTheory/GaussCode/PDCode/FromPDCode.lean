/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.GaussCode.PDCode.Components

/-!
# Outgoing crossing data of an oriented PD-code

A traversal of an oriented PD-code visits one outgoing half-edge for each local strand at every
crossing.  This file records the resulting finite equivalence with crossing names and the two
strand choices.  It is the cardinality and indexing prerequisite for reconstructing a based Gauss
code from a one-component PD-code; link-level traversal and basepoint choices remain separate.
-/

public section

namespace TauCeti

namespace OrientedPDCode

variable {n : ℕ}

/-- The crossing and local-strand data carried by an outgoing half-edge.

The second coordinate is `false` for the `0`--`2` strand and `true` for the `1`--`3` strand. -/
noncomputable def outgoingData (D : OrientedPDCode n) :
    {h : Fin (4 * n) // D.orientation h = true} → Fin n × Bool := fun h =>
  let x := (PDCode.crossingSlotEquiv n).symm (D.toPDCode.halfEdge.symm h.1)
  (x.1, decide (x.2 = 1 ∨ x.2 = 3))

private theorem orientation_opposite (D : OrientedPDCode n) (i : Fin n) (s : Fin 4) :
    D.orientation (D.crossing i (PDCode.oppositeCrossingSlot s)) =
      !D.orientation (D.crossing i s) := by
  rw [PDCode.crossing_apply, PDCode.crossing_apply]
  exact D.orientation_oppositeCrossingSlot i s

private theorem not_both_outgoing (D : OrientedPDCode n) (i : Fin n) (s : Fin 4) :
    ¬(D.orientation (D.crossing i s) = true ∧
      D.orientation (D.crossing i (PDCode.oppositeCrossingSlot s)) = true) := by
  rintro ⟨hs, hopp⟩
  have ho := D.orientation_opposite i s
  rw [hs, hopp] at ho
  simp at ho

private theorem outgoingData_injective (D : OrientedPDCode n) :
    Function.Injective D.outgoingData := by
  intro h k hk
  let x := (PDCode.crossingSlotEquiv n).symm (D.toPDCode.halfEdge.symm h.1)
  let y := (PDCode.crossingSlotEquiv n).symm (D.toPDCode.halfEdge.symm k.1)
  have hxy : x.1 = y.1 ∧ decide (x.2 = 1 ∨ x.2 = 3) =
      decide (y.2 = 1 ∨ y.2 = 3) := by
    simpa [outgoingData, x, y] using hk
  have hx : D.orientation (D.crossing x.1 x.2) = true := by
    simpa [x, PDCode.crossing_apply] using h.property
  have hy : D.orientation (D.crossing y.1 y.2) = true := by
    simpa [y, PDCode.crossing_apply] using k.property
  have hslot : x.2 = y.2 := by
    rcases x with ⟨i, s⟩
    rcases y with ⟨j, t⟩
    simp only at hxy hx hy ⊢
    have hij := hxy.1
    subst j
    fin_cases s <;> fin_cases t <;> simp at hxy
    all_goals try (apply Fin.ext; rfl)
    · exfalso
      exact (not_both_outgoing D i 0) ⟨
        hx, (by simpa [PDCode.oppositeCrossingSlot_apply] using hy)⟩
    · exfalso
      exact (not_both_outgoing D i 1) ⟨
        hx, (by simpa [PDCode.oppositeCrossingSlot_apply] using hy)⟩
    · exfalso
      exact (not_both_outgoing D i 0) ⟨
        hy, (by simpa [PDCode.oppositeCrossingSlot_apply] using hx)⟩
    · exfalso
      exact (not_both_outgoing D i 1) ⟨
        hy, (by simpa [PDCode.oppositeCrossingSlot_apply] using hx)⟩
  have hxy' : x = y := Prod.ext hxy.1 hslot
  have hhalf : D.toPDCode.halfEdge.symm h.1 = D.toPDCode.halfEdge.symm k.1 := by
    simpa [x, y] using congrArg (PDCode.crossingSlotEquiv n) hxy'
  apply Subtype.ext
  exact D.toPDCode.halfEdge.injective (by simpa using congrArg D.toPDCode.halfEdge hhalf)

private noncomputable def chooseOutgoingSlot (D : OrientedPDCode n) (i : Fin n) (b : Bool) :
    Fin 4 :=
  if b then if D.orientation (D.crossing i 1) then 1 else 3
  else if D.orientation (D.crossing i 0) then 0 else 2

private theorem chooseOutgoingSlot_orientation (D : OrientedPDCode n) (i : Fin n) (b : Bool) :
    D.orientation (D.crossing i (D.chooseOutgoingSlot i b)) = true := by
  classical
  by_cases hb : b
  · simp only [chooseOutgoingSlot, hb, ↓reduceIte]
    split_ifs with hs
    · exact hs
    · have ho := D.orientation_opposite i 1
      have hfalse := Bool.eq_false_of_not_eq_true hs
      rw [hfalse] at ho
      simpa [PDCode.oppositeCrossingSlot_apply] using ho
  · simp only [chooseOutgoingSlot, hb, Bool.false_eq_true, ↓reduceIte]
    split_ifs with hs
    · exact hs
    · have ho := D.orientation_opposite i 0
      have hfalse := Bool.eq_false_of_not_eq_true hs
      rw [hfalse] at ho
      simpa [PDCode.oppositeCrossingSlot_apply] using ho

private theorem outgoingData_surjective (D : OrientedPDCode n) :
    Function.Surjective D.outgoingData := by
  classical
  intro x
  rcases x with ⟨i, b⟩
  let s := D.chooseOutgoingSlot i b
  have hs : D.orientation (D.crossing i s) = true :=
    D.chooseOutgoingSlot_orientation i b
  let h : {h : Fin (4 * n) // D.orientation h = true} := ⟨D.crossing i s, hs⟩
  refine ⟨h, ?_⟩
  cases b <;>
    dsimp [outgoingData, h, s, chooseOutgoingSlot] <;>
    split_ifs <;> simp

/-- Every crossing has two outgoing half-edges, one on each local strand. -/
noncomputable def outgoingDataEquiv (D : OrientedPDCode n) :
    {h : Fin (4 * n) // D.orientation h = true} ≃ Fin n × Bool :=
  Equiv.ofBijective D.outgoingData ⟨D.outgoingData_injective, D.outgoingData_surjective⟩

@[simp]
theorem outgoingDataEquiv_apply (D : OrientedPDCode n)
    (h : {h : Fin (4 * n) // D.orientation h = true}) :
    D.outgoingDataEquiv h = D.outgoingData h :=
  Equiv.ofBijective_apply _ _ _

/-- The outgoing half-edge carrier has cardinality `2 * n`. -/
theorem card_outgoing (D : OrientedPDCode n) :
    Fintype.card {h : Fin (4 * n) // D.orientation h = true} = 2 * n := by
  rw [Fintype.card_congr D.outgoingDataEquiv]
  simp [Nat.mul_comm]

end OrientedPDCode

end TauCeti
