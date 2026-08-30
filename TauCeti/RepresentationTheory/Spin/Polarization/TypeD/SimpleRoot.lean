/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.SimpleRoot
public import TauCeti.RepresentationTheory.Spin.Polarization.TypeD
/-!
# Type-D simple roots on the spin module

The split type-`D` simple-root matrices are transported to quadratic Clifford elements. Their
positive-root actions kill the exterior vectors with all signs positive and with only the final
sign negative. These are the two vectors carrying the fork-node half-spin highest weights.

## References

* [Tau Ceti Roadmap, Spin Representations, Layer 5](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md#layer-5-the-fundamental-representations-of-b%E2%82%97-and-d%E2%82%97)
-/

public section

open CliffordAlgebra QuadraticMap

namespace TauCeti

universe u v

namespace SpinPolarizationData

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} (P : SpinPolarizationData Q) (n : ℕ) (hn : 4 ≤ n)
  (b : Module.Basis (Fin n) K P.W) [Invertible (2 : K)]

@[simp] private theorem sum_ite_and_eq (f : Fin n → V) (i : Fin n) (p : Prop)
    [Decidable p] :
    (∑ j, if j = i ∧ p then f j else 0) = if p then f i else 0 := by
  by_cases hp : p <;> simp [hp]

private theorem typeDQuadraticEquiv_eq_bivector_of_apply (hline : P.line = ⊥)
    (A : LieAlgebra.Orthogonal.typeD (Fin n) K) (u v : V)
    (hA : ∀ j, (LinearMap.toMatrixAlgEquiv (P.typeDBasis b hline)).symm A
      (P.typeDBasis b hline j) = QuadraticMap.polar Q v (P.typeDBasis b hline j) • u -
        QuadraticMap.polar Q u (P.typeDBasis b hline j) • v) :
    P.typeDQuadraticEquiv b hline A =
      ⟨bivector Q u v, bivector_mem_quadraticLieSubalgebra Q u v⟩ := by
  let _ : Module.Finite K V := Module.Finite.of_basis (P.typeDBasis b hline)
  apply quadraticLieSubalgebra_ext Q (P.nondegenerate_of_line_eq_bot hline)
  intro x
  rw [P.typeDQuadraticEquiv_lie_ι b hline, bivector_lie_ι]
  have hmap : (LinearMap.toMatrixAlgEquiv (P.typeDBasis b hline)).symm A =
      (Q.polarBilin v).smulRight u - (Q.polarBilin u).smulRight v := by
    apply (P.typeDBasis b hline).ext
    intro j
    simpa only [LinearMap.sub_apply, LinearMap.smulRight_apply,
      QuadraticMap.polarBilin_apply_apply] using hA j
  rw [hmap]
  simp only [LinearMap.sub_apply, LinearMap.smulRight_apply,
    QuadraticMap.polarBilin_apply_apply]

/-- Under the polarization comparison, a chain simple-root operator is the bivector formed from
the corresponding basis vector and the next dual vector. -/
@[simp]
theorem typeDQuadraticEquiv_typeDSimpleRootOperator_of_chain (hline : P.line = ⊥) (i : Fin n)
    (hi : (i : ℕ) + 1 < n) :
    P.typeDQuadraticEquiv b hline
        (LieAlgebra.Orthogonal.typeDSimpleRootOperator (K := K) n hn i) =
  ⟨bivector Q (b i : V) (P.dualVector b ⟨(i : ℕ) + 1, hi⟩ : V),
        bivector_mem_quadraticLieSubalgebra Q _ _⟩ := by
  apply P.typeDQuadraticEquiv_eq_bivector_of_apply n b hline
  rintro (j | j)
  · rw [LinearMap.toMatrixAlgEquiv_symm, Matrix.toLinAlgEquiv_self, P.typeDBasis_inl]
    rw [P.polar_W_eq_zero, zero_smul, sub_zero, QuadraticMap.polar_comm,
      P.polar_dualVector]
    simp [LieAlgebra.Orthogonal.typeDSimpleRootMatrix_of_chain n hn i hi,
      Matrix.single_apply, eq_comm]
    simpa only [eq_comm] using
      (sum_ite_and_eq (n := n) (fun x ↦ (b x : V)) i
        ((⟨(i : ℕ) + 1, hi⟩ : Fin n) = j)).symm
  · rw [LinearMap.toMatrixAlgEquiv_symm, Matrix.toLinAlgEquiv_self, P.typeDBasis_inr]
    rw [P.polar_W'_eq_zero, zero_smul, zero_sub, P.polar_dualVector]
    simp [LieAlgebra.Orthogonal.typeDSimpleRootMatrix_of_chain n hn i hi,
      Matrix.single_apply, eq_comm]

/-- Under the polarization comparison, the fork simple-root operator is the bivector of the final
two isotropic basis vectors. -/
@[simp]
theorem typeDQuadraticEquiv_typeDSimpleRootOperator_of_fork (hline : P.line = ⊥) (i : Fin n)
    (hi : ¬(i : ℕ) + 1 < n) :
    P.typeDQuadraticEquiv b hline
        (LieAlgebra.Orthogonal.typeDSimpleRootOperator (K := K) n hn i) =
      ⟨bivector Q (b ⟨n - 2, by omega⟩ : V) (b ⟨n - 1, by omega⟩ : V),
        bivector_mem_quadraticLieSubalgebra Q _ _⟩ := by
  apply P.typeDQuadraticEquiv_eq_bivector_of_apply n b hline
  rintro (j | j)
  · rw [LinearMap.toMatrixAlgEquiv_symm, Matrix.toLinAlgEquiv_self, P.typeDBasis_inl]
    simp only [P.polar_W_eq_zero, zero_smul, sub_self]
    simp [LieAlgebra.Orthogonal.typeDSimpleRootMatrix_of_fork n hn i hi]
  · rw [LinearMap.toMatrixAlgEquiv_symm, Matrix.toLinAlgEquiv_self, P.typeDBasis_inr]
    rw [P.polar_dualVector, P.polar_dualVector]
    simp [LieAlgebra.Orthogonal.typeDSimpleRootMatrix_of_fork n hn i hi,
      Matrix.single_apply, Finset.sum_sub_distrib, sub_smul, eq_comm]

/-- The exterior vector with all type-`D` spin signs positive. -/
noncomputable def typeDPositiveSpinVector : ExteriorAlgebra K P.W :=
  b.ExteriorAlgebra Finset.univ

/-- The exterior vector obtained by changing only the final type-`D` spin sign. -/
noncomputable def typeDFinalNegativeSpinVector : ExteriorAlgebra K P.W :=
  b.ExteriorAlgebra (Finset.univ.erase ⟨n - 1, by omega⟩)

omit [Invertible (2 : K)] in
private theorem wedge_basis_eq_zero_of_mem (i : Fin n) (s : Finset (Fin n)) (hi : i ∈ s) :
    P.wedge (b i) (b.ExteriorAlgebra s) = 0 := by
  rw [P.wedge_apply]
  have hocc := ExteriorAlgebra.ι_mul_contractLeft_coord_basis b i s
  simp only [hi, ↓reduceIte] at hocc
  rw [← hocc, ← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul]

private theorem spinAction_typeDSimpleRootOperator_basis_eq_zero
    (hline : P.line = ⊥) (i : Fin n) (s : Finset (Fin n))
    (hi : (i : ℕ) + 1 < n → i ∈ s)
    (hfork : ¬(i : ℕ) + 1 < n → (⟨n - 2, by omega⟩ : Fin n) ∈ s) :
    spinAction Q P
        (P.typeDQuadraticEquiv b hline
          (LieAlgebra.Orthogonal.typeDSimpleRootOperator (K := K) n hn i))
        (b.ExteriorAlgebra s) = 0 := by
  by_cases hchain : (i : ℕ) + 1 < n
  · rw [P.typeDQuadraticEquiv_typeDSimpleRootOperator_of_chain n hn b hline i hchain]
    have hw := P.wedge_basis_eq_zero_of_mem n b i s (hi hchain)
    have hcontract : P.wedge (b i)
        (P.contract (P.dualVector b ⟨(i : ℕ) + 1, hchain⟩) (b.ExteriorAlgebra s)) = 0 := by
      have hc := congrArg
        (P.contract (P.dualVector b ⟨(i : ℕ) + 1, hchain⟩)) hw
      rw [map_zero, P.contract_wedge] at hc
      simpa [P.polar_dualVector, Fin.ext_iff] using hc
    rw [P.wedge_apply, P.contract_apply, P.pairingEquiv_dualVector] at hcontract
    simp only [bivector_def, map_smul, map_sub, map_mul, spinAction_ι,
      P.cliffordOperator_coe_W, P.cliffordOperator_coe_W', LinearMap.smul_apply,
      LinearMap.sub_apply, Module.End.mul_apply]
    rw [P.contract_wedge]
    simp [hcontract, P.polar_dualVector, Fin.ext_iff]
  · rw [P.typeDQuadraticEquiv_typeDSimpleRootOperator_of_fork n hn b hline i hchain]
    simp only [bivector_def, map_smul, map_sub, map_mul, spinAction_ι,
      P.cliffordOperator_coe_W, LinearMap.smul_apply, LinearMap.sub_apply,
      Module.End.mul_apply]
    have hp := P.wedge_basis_eq_zero_of_mem n b ⟨n - 2, by omega⟩ s (hfork hchain)
    have hswap := ExteriorAlgebra.ι_add_mul_swap (R := K)
      (b ⟨n - 2, by omega⟩) (b ⟨n - 1, by omega⟩)
    simp only [P.wedge_apply] at hp ⊢
    have hfirst : (ExteriorAlgebra.ι K) (b ⟨n - 2, by omega⟩) *
        ((ExteriorAlgebra.ι K) (b ⟨n - 1, by omega⟩) * b.ExteriorAlgebra s) = 0 := by
      rw [← mul_assoc, eq_neg_of_add_eq_zero_left hswap, neg_mul, mul_assoc, hp, mul_zero,
        neg_zero]
    simp [hfirst, hp]

/-- Every positive simple-root operator kills the exterior vector with all spin signs positive. -/
theorem spinAction_typeDSimpleRootOperator_positive_eq_zero (hline : P.line = ⊥) (i : Fin n) :
    spinAction Q P
        (P.typeDQuadraticEquiv b hline
          (LieAlgebra.Orthogonal.typeDSimpleRootOperator (K := K) n hn i))
        (P.typeDPositiveSpinVector n b) = 0 := by
  apply P.spinAction_typeDSimpleRootOperator_basis_eq_zero n hn b hline i Finset.univ
  · simp
  · simp

/-- Every positive simple-root operator kills the exterior vector with only its final spin sign
negative. -/
theorem spinAction_typeDSimpleRootOperator_finalNegative_eq_zero (hline : P.line = ⊥)
    (i : Fin n) :
    spinAction Q P
        (P.typeDQuadraticEquiv b hline
          (LieAlgebra.Orthogonal.typeDSimpleRootOperator (K := K) n hn i))
        (P.typeDFinalNegativeSpinVector n hn b) = 0 := by
  apply P.spinAction_typeDSimpleRootOperator_basis_eq_zero n hn b hline i
      (Finset.univ.erase ⟨n - 1, by omega⟩)
  · intro hi
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    intro h
    have hv : (i : ℕ) = n - 1 := congrArg Fin.val h
    omega
  · intro _
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    intro h
    have hv : n - 2 = n - 1 := congrArg Fin.val h
    omega

end SpinPolarizationData

end TauCeti
