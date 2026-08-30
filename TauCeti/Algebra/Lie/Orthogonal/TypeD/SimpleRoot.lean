/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.DiagonalCartan
public import TauCeti.LinearAlgebra.RootSystem.ClassicalTypeD

/-!
# Simple-root operators in the split type-D Lie algebra

This file realizes the Bourbaki simple roots of `Dₙ` as explicit matrices in the split orthogonal
Lie algebra. The chain root `εᵢ - εᵢ₊₁` is represented in the diagonal blocks, while the fork root
`εₙ₋₂ + εₙ₋₁` is represented in the upper-right skew block.

## References

* [Tau Ceti Roadmap, Spin Representations, Layer 5](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md#layer-5-the-fundamental-representations-of-b%E2%82%97-and-d%E2%82%97)
-/

public section

universe u

namespace LieAlgebra.Orthogonal

variable {K : Type u} [CommRing K]

/-- The ambient matrix of the Bourbaki-numbered simple-root operator of type `Dₙ`. -/
def typeDSimpleRootMatrix (n : ℕ) (hn : 4 ≤ n) (i : Fin n) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  if hi : (i : ℕ) + 1 < n then
    Matrix.fromBlocks
      (Matrix.single i ⟨(i : ℕ) + 1, hi⟩ 1) 0 0
      (-Matrix.single ⟨(i : ℕ) + 1, hi⟩ i 1)
  else
    Matrix.fromBlocks 0
      (Matrix.single ⟨n - 2, by omega⟩ ⟨n - 1, by omega⟩ 1 -
        Matrix.single ⟨n - 1, by omega⟩ ⟨n - 2, by omega⟩ 1)
      0 0

/-- The matrix of a chain simple root `εᵢ - εᵢ₊₁`. -/
@[simp]
theorem typeDSimpleRootMatrix_of_chain (n : ℕ) (hn : 4 ≤ n) (i : Fin n)
    (hi : (i : ℕ) + 1 < n) :
    typeDSimpleRootMatrix (K := K) n hn i =
      Matrix.fromBlocks (Matrix.single i ⟨(i : ℕ) + 1, hi⟩ 1) 0 0
        (-Matrix.single ⟨(i : ℕ) + 1, hi⟩ i 1) := by
  rw [typeDSimpleRootMatrix, dite_eq_left hi]

/-- The matrix of the fork simple root `εₙ₋₁ + εₙ`. -/
@[simp]
theorem typeDSimpleRootMatrix_of_fork (n : ℕ) (hn : 4 ≤ n) (i : Fin n)
    (hi : ¬(i : ℕ) + 1 < n) :
    typeDSimpleRootMatrix (K := K) n hn i = Matrix.fromBlocks 0
      (Matrix.single ⟨n - 2, by omega⟩ ⟨n - 1, by omega⟩ 1 -
        Matrix.single ⟨n - 1, by omega⟩ ⟨n - 2, by omega⟩ 1) 0 0 := by
  rw [typeDSimpleRootMatrix, dite_eq_right hi]

/-- Every standard type-`D` simple-root matrix is skew-adjoint for the split form. -/
theorem typeDSimpleRootMatrix_mem_typeD (n : ℕ) (hn : 4 ≤ n) (i : Fin n) :
    typeDSimpleRootMatrix (K := K) n hn i ∈
      LieAlgebra.Orthogonal.typeD (Fin n) K := by
  rw [LieAlgebra.Orthogonal.typeD, mem_skewAdjointMatricesLieSubalgebra,
    mem_skewAdjointMatricesSubmodule, Matrix.IsSkewAdjoint, Matrix.IsAdjointPair]
  rw [typeDSimpleRootMatrix]
  split_ifs with hi
  · ext (a | a) (b | b) <;>
      simp [JD, Matrix.fromBlocks_transpose,
        Matrix.fromBlocks_multiply, Matrix.single_apply]
  · ext (a | a) (b | b) <;>
      simp [JD, Matrix.fromBlocks_transpose,
        Matrix.fromBlocks_multiply, Matrix.single_apply]

/-- The Bourbaki-numbered simple-root operator in the split orthogonal Lie algebra of type `Dₙ`. -/
def typeDSimpleRootOperator (n : ℕ) (hn : 4 ≤ n) (i : Fin n) :
    LieAlgebra.Orthogonal.typeD (Fin n) K :=
  ⟨typeDSimpleRootMatrix (K := K) n hn i, typeDSimpleRootMatrix_mem_typeD n hn i⟩

@[simp]
theorem coe_typeDSimpleRootOperator (n : ℕ) (hn : 4 ≤ n) (i : Fin n) :
    (typeDSimpleRootOperator (K := K) n hn i : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
      typeDSimpleRootMatrix (K := K) n hn i :=
  (rfl)

end LieAlgebra.Orthogonal

namespace TauCeti

/-- The Bourbaki simple root, with its integral coordinates cast into the coefficient ring. -/
noncomputable def typeDSimpleRootWeight (K : Type u) [CommRing K]
    (n : ℕ) (hn : 4 ≤ n) (i : Fin n) : Module.Dual K (typeDDiagonalCartan K (Fin n)) :=
  typeDWeightEquiv (K := K) (ι := Fin n) fun j => (DynkinType.typeDSimpleRoot n hn i j : K)

@[simp]
theorem typeDSimpleRootWeight_typeDDiagonalEquiv (K : Type u) [CommRing K]
    (n : ℕ) (hn : 4 ≤ n) (i : Fin n) (d : Fin n → K) :
    typeDSimpleRootWeight K n hn i (typeDDiagonalEquiv (K := K) (ι := Fin n) d) =
      if hi : (i : ℕ) + 1 < n then d i - d ⟨(i : ℕ) + 1, hi⟩
      else d ⟨n - 2, by omega⟩ + d ⟨n - 1, by omega⟩ := by
  split_ifs with hi
  · rw [typeDSimpleRootWeight, typeDWeightEquiv_apply,
      DynkinType.typeDSimpleRoot_of_add_one_lt hn hi]
    simp_rw [Pi.sub_apply, Int.cast_sub, sub_mul]
    rw [Finset.sum_sub_distrib]
    simp [Pi.single_apply]
  · rw [typeDSimpleRootWeight, typeDWeightEquiv_apply,
      DynkinType.typeDSimpleRoot_of_not_add_one_lt hn hi]
    simp_rw [Pi.add_apply, Int.cast_add, add_mul]
    rw [Finset.sum_add_distrib]
    simp [Pi.single_apply]

private theorem lie_typeDSimpleRootOperator_typeDDiagonalEquiv
    {K : Type u} [CommRing K] (n : ℕ) (hn : 4 ≤ n) (i : Fin n) (d : Fin n → K) :
    ⁅(typeDDiagonalEquiv (K := K) (ι := Fin n) d : typeDDiagonalCartan K (Fin n)),
        LieAlgebra.Orthogonal.typeDSimpleRootOperator (K := K) n hn i⁆ =
      typeDSimpleRootWeight K n hn i
        (typeDDiagonalEquiv (K := K) (ι := Fin n) d) •
        LieAlgebra.Orthogonal.typeDSimpleRootOperator (K := K) n hn i := by
  apply Subtype.ext
  by_cases hi : (i : ℕ) + 1 < n
  · ext (a | a) (b | b) <;>
      simp [typeDSimpleRootWeight_typeDDiagonalEquiv,
        LieAlgebra.Orthogonal.typeDSimpleRootOperator,
        LieAlgebra.Orthogonal.typeDSimpleRootMatrix, hi, Matrix.single_apply]
    · split_ifs with h
      · obtain ⟨ha, hb⟩ := h
        subst a
        subst b
        rfl
      · rfl
    · split_ifs with h
      · obtain ⟨hb, ha⟩ := h
        subst b
        subst a
        ring
      · rfl
  · ext (a | a) (b | b) <;>
      simp [typeDSimpleRootWeight_typeDDiagonalEquiv,
        LieAlgebra.Orthogonal.typeDSimpleRootOperator,
        LieAlgebra.Orthogonal.typeDSimpleRootMatrix, hi, Matrix.single_apply]
    · by_cases h₁ : (⟨n - 2, by omega⟩ : Fin n) = a ∧
          (⟨n - 1, by omega⟩ : Fin n) = b
      · obtain ⟨ha, hb⟩ := h₁
        subst a
        subst b
        simp
      · by_cases h₂ : (⟨n - 1, by omega⟩ : Fin n) = a ∧
            (⟨n - 2, by omega⟩ : Fin n) = b
        · obtain ⟨ha, hb⟩ := h₂
          subst a
          subst b
          simp
          ring
        · simp [h₁, h₂]

/-- The standard simple-root operator has the corresponding root-space equation for the split
diagonal Cartan. -/
theorem lie_typeDSimpleRootOperator {K : Type u} [CommRing K]
    (n : ℕ) (hn : 4 ≤ n) (i : Fin n) (H : typeDDiagonalCartan K (Fin n)) :
    ⁅H, LieAlgebra.Orthogonal.typeDSimpleRootOperator (K := K) n hn i⁆ =
      typeDSimpleRootWeight K n hn i H •
        LieAlgebra.Orthogonal.typeDSimpleRootOperator (K := K) n hn i := by
  rw [← (typeDDiagonalEquiv (K := K) (ι := Fin n)).apply_symm_apply H]
  exact lie_typeDSimpleRootOperator_typeDDiagonalEquiv n hn i _

end TauCeti
