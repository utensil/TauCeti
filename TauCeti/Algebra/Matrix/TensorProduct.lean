/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MatrixAlgebra
public import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Tensor products and composition of finite matrix algebras

Mathlib identifies tensor products and nested matrices using product index types. This file
reindexes those equivalences along `Fin m × Fin n ≃ Fin (m * n)`, the form used by finite matrix
algebras throughout TauCeti.
-/

public section

open scoped TensorProduct

universe u v w

namespace TauCeti.Matrix

/-- **Matrix absorption**:
`Mₘ(A) ⊗[R] Mₙ(B) ≃ₐ[R] Mₘₙ(A ⊗[R] B)` for arbitrary algebras and sizes. -/
def kroneckerTMulFinAlgEquiv (m n : ℕ) (R : Type u) [CommSemiring R]
    (A : Type v) [Semiring A] [Algebra R A] (B : Type w) [Semiring B] [Algebra R B] :
    Matrix (Fin m) (Fin m) A ⊗[R] Matrix (Fin n) (Fin n) B ≃ₐ[R]
      Matrix (Fin (m * n)) (Fin (m * n)) (A ⊗[R] B) :=
  (Matrix.kroneckerTMulAlgEquiv (Fin m) (Fin n) R R A B).trans
    (Matrix.reindexAlgEquiv R _ finProdFinEquiv)

@[simp]
theorem kroneckerTMulFinAlgEquiv_tmul_apply (m n : ℕ) (R : Type u) [CommSemiring R]
    (A : Type v) [Semiring A] [Algebra R A] (B : Type w) [Semiring B] [Algebra R B]
    (M : Matrix (Fin m) (Fin m) A) (N : Matrix (Fin n) (Fin n) B) (i j : Fin (m * n)) :
    kroneckerTMulFinAlgEquiv m n R A B (M ⊗ₜ N) i j =
      M (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm j).1 ⊗ₜ[R]
        N (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm j).2 := by
  simp [kroneckerTMulFinAlgEquiv, Matrix.coe_reindexAlgEquiv, finProdFinEquiv]

/-- The scalar specialization `Mₘ(R) ⊗[R] Mₙ(R) ≃ₐ[R] Mₘₙ(R)`. -/
def kroneckerFinAlgEquiv (m n : ℕ) (R : Type u) [CommSemiring R] :
    Matrix (Fin m) (Fin m) R ⊗[R] Matrix (Fin n) (Fin n) R ≃ₐ[R]
      Matrix (Fin (m * n)) (Fin (m * n)) R :=
  (Matrix.kroneckerAlgEquiv (Fin m) (Fin n) R).trans
    (Matrix.reindexAlgEquiv R R finProdFinEquiv)

@[simp]
theorem kroneckerFinAlgEquiv_tmul_apply (m n : ℕ) (R : Type u) [CommSemiring R]
    (M : Matrix (Fin m) (Fin m) R) (N : Matrix (Fin n) (Fin n) R) (i j : Fin (m * n)) :
    kroneckerFinAlgEquiv m n R (M ⊗ₜ N) i j =
      M (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm j).1 *
        N (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm j).2 := by
  simp [kroneckerFinAlgEquiv, Matrix.coe_reindexAlgEquiv, finProdFinEquiv]

/-- Flatten nested finite matrices: `Mₘ(Mₙ(A)) ≃ₐ[R] Mₘₙ(A)`. -/
def compFinAlgEquiv (m n : ℕ) (R : Type u) [CommSemiring R]
    (A : Type v) [Semiring A] [Algebra R A] :
    Matrix (Fin m) (Fin m) (Matrix (Fin n) (Fin n) A) ≃ₐ[R]
      Matrix (Fin (m * n)) (Fin (m * n)) A :=
  (Matrix.compAlgEquiv (Fin m) (Fin n) A R).trans
    (Matrix.reindexAlgEquiv R A finProdFinEquiv)

@[simp]
theorem compFinAlgEquiv_apply (m n : ℕ) (R : Type u) [CommSemiring R]
    (A : Type v) [Semiring A] [Algebra R A]
    (M : Matrix (Fin m) (Fin m) (Matrix (Fin n) (Fin n) A)) (i j : Fin (m * n)) :
    compFinAlgEquiv m n R A M i j =
      M (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm j).1
        (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm j).2 := by
  simp [compFinAlgEquiv, Matrix.coe_reindexAlgEquiv, finProdFinEquiv]

end TauCeti.Matrix
