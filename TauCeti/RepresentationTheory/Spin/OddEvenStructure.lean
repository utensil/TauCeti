/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.EvenIsometry
public import TauCeti.RepresentationTheory.Spin.Structure
import TauCeti.LinearAlgebra.QuadraticForm.Radical
import TauCeti.LinearAlgebra.QuadraticForm.SepClosed

/-!
# The even Clifford algebra in odd dimension

Over a separably closed field, the even Clifford algebra of a nondegenerate quadratic space of
dimension `2 * l + 1` is a matrix algebra of size `2 ^ l`.
-/

public section

namespace CliffordAlgebra

open Module QuadraticMap

universe u v

variable {F : Type u} [Field F] [NeZero (2 : F)] [IsSepClosed F]
  {V : Type v} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V}

/-- The even Clifford algebra of a nondegenerate quadratic form in dimension `2 * l + 1` is the
matrix algebra `M_{2^l}(F)`. -/
theorem nonempty_even_algEquiv_matrix_of_finrank_eq_two_mul_add_one {l : ℕ}
    (hQ : Q.Nondegenerate) (hV : finrank F V = 2 * l + 1) :
    Nonempty (CliffordAlgebra.even Q ≃ₐ[F] Matrix (Fin (2 ^ l)) (Fin (2 ^ l)) F) := by
  let _ : Invertible (2 : F) := invertibleOfNonzero (NeZero.ne (2 : F))
  let W := Fin (2 * l) → F
  let Q₀ : QuadraticForm F W := QuadraticMap.weightedSumSquares F (1 : Fin (2 * l) → F)
  let Q₁ : QuadraticForm F (W × F) := CliffordAlgebra.EquivEven.Q' Q₀
  let e : V ≃ₗ[F] W × F := LinearEquiv.ofFinrankEq V (W × F) (by
    simp only [W, finrank_prod, finrank_fintype_fun_eq_card, Fintype.card_fin, finrank_self]
    omega)
  have hQ₀rad : Q₀.radical = ⊥ := by
    rw [show Q₀ = QuadraticMap.weightedSumSquares F (1 : Fin (2 * l) → F) from rfl,
      QuadraticForm.radical_weightedSumSquares, Submodule.eq_bot_iff]
    intro v hv
    funext j
    exact Pi.mem_spanSubset_iff.1 hv j (by simp)
  have hsrad : (-QuadraticMap.sq (R := F) (A := F)).radical = ⊥ := by
    rw [QuadraticMap.radical_neg, Submodule.eq_bot_iff]
    intro x hx
    exact mul_self_eq_zero.mp (QuadraticMap.mem_radical_iff'.1 hx).1
  have hQ₁ : Q₁.Nondegenerate :=
    QuadraticMap.nondegenerate_iff_radical_eq_bot.mpr (by
      rw [show Q₁ = Q₀.prod (-QuadraticMap.sq (R := F) (A := F)) from rfl,
        QuadraticMap.radical_prod, hQ₀rad, hsrad]
      simp)
  let Q' : QuadraticForm F V := Q₁.comp e.toLinearMap
  have hQ'assoc : (QuadraticMap.associated Q').SeparatingLeft := by
    have hQ₁assoc : (QuadraticMap.associated Q₁).Nondegenerate :=
      QuadraticMap.nondegenerate_associated_iff.mpr hQ₁
    rw [show Q' = Q₁.comp e.toLinearMap from rfl, QuadraticMap.associated_comp]
    intro x hx
    apply e.injective
    rw [map_zero]
    apply hQ₁assoc.1 (e x)
    intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    simpa [LinearMap.compl₁₂_apply] using hx z
  let eqv : Q.IsometryEquiv Q' := ((QuadraticForm.equivalent_weightedSumSquares_of_isSepClosed Q
    (QuadraticMap.nondegenerate_associated_iff.mpr hQ).1).trans
      (QuadraticForm.equivalent_weightedSumSquares_of_isSepClosed Q' hQ'assoc).symm).some
  let eqv₁ : Q.IsometryEquiv Q₁ :=
    eqv.trans (QuadraticMap.isometryEquivOfCompLinearEquiv Q₁ e).symm
  let hmat := Classical.choice (CliffordAlgebra.nonempty_algEquiv_matrix_of_finrank_eq_two_mul
    (Q := Q₀) (l := l) (QuadraticMap.nondegenerate_iff_radical_eq_bot.mpr hQ₀rad)
      (by simp [W]))
  exact ⟨(CliffordAlgebra.evenEquivOfIsometry eqv₁).trans
    ((CliffordAlgebra.equivEven Q₀).symm.trans hmat)⟩

end CliffordAlgebra
