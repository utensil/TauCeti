/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Spin.Exceptional.Three


/-!
# The Spin group in dimension three

The matrix model of the even Clifford algebra in dimension three sends Clifford reversal to
matrix adjugation.  The Spin norm equation therefore becomes the determinant-one equation and
gives an injective homomorphism from the Spin group to `SL₂`.

Surjectivity remains downstream: it requires proving that the determinant-one matrices lie in
the image of the Lipschitz-generated Spin group.

## Main results

* `TauCeti.spin3ToSL2`: the homomorphism from `spinGroup Q` to `SL₂` induced by the even
  Clifford matrix model.
* `TauCeti.spin3ToSL2_injective`: this homomorphism is injective.

## References

This is the determinant-one direction of the `Spin₃ ≃ SL₂` target in Layer 6 of the
SpinRepresentations roadmap.  See Fulton and Harris, *Representation Theory: A First Course*,
Lecture 20.
-/

public section

universe u v

open CliffordAlgebra

namespace TauCeti

variable {K : Type u} [Field K] [NeZero (2 : K)] [IsSepClosed K]
  {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (Q : QuadraticForm K V)

private noncomputable def spin3MatrixHom
    (hQ : Q.Nondegenerate) (hV : Module.finrank K V = 3) :
    spinGroup Q →* Matrix (Fin 2) (Fin 2) K :=
  (evenEquivMatrixTwoOfFinrankThree Q hQ hV).toAlgHom.toMonoidHom.comp
    (spinGroupToEven Q)

private theorem spin3MatrixHom_apply
    (hQ : Q.Nondegenerate) (hV : Module.finrank K V = 3) (g : spinGroup Q) :
    spin3MatrixHom Q hQ hV g =
      evenEquivMatrixTwoOfFinrankThree Q hQ hV (spinGroupToEven Q g) :=
  rfl

private theorem spin3Matrix_det
    (hQ : Q.Nondegenerate) (hV : Module.finrank K V = 3) (g : spinGroup Q) :
    Matrix.det (spin3MatrixHom Q hQ hV g) = 1 := by
  let e := evenEquivMatrixTwoOfFinrankThree Q hQ hV
  let x := spinGroupToEven Q g
  have hstar : star (g : CliffordAlgebra Q) * g = 1 :=
    spinGroup.star_mul_self_of_mem g.property
  have hreverse_g : reverse (g : CliffordAlgebra Q) * g = 1 := by
    simpa only [CliffordAlgebra.star_def, spinGroup.involute_eq g.property] using hstar
  have hx : (x : CliffordAlgebra Q) = g := coe_spinGroupToEven_apply Q g
  have hreverse : reverse (x : CliffordAlgebra Q) * x = 1 := by
    rw [hx]
    exact hreverse_g
  have hmul :
      (⟨reverse (x : CliffordAlgebra Q),
          (reverse_mem_evenOdd_iff Q).2 x.property⟩ : ↥(even Q)) * x = 1 := by
    apply Subtype.ext
    exact hreverse
  have hrev := evenEquivMatrixTwoOfFinrankThree_reverse Q hQ hV x
  have hmatrix : Matrix.adjugate (e x) * e x = 1 := by
    rw [← hrev, ← map_mul, hmul, map_one]
  have hscalar : Matrix.det (e x) • (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
    rw [← Matrix.adjugate_mul]
    exact hmatrix
  have h00 := congrFun (congrFun hscalar (0 : Fin 2)) (0 : Fin 2)
  have hdet : Matrix.det (e x) = 1 := by simpa using h00
  rw [spin3MatrixHom_apply]
  exact hdet

/-- The injective homomorphism from the three-dimensional Spin group to `SL₂` induced by the
chosen matrix model of the even Clifford algebra. -/
noncomputable def spin3ToSL2
    (hQ : Q.Nondegenerate) (hV : Module.finrank K V = 3) :
    spinGroup Q →* Matrix.SpecialLinearGroup (Fin 2) K where
  toFun g := ⟨spin3MatrixHom Q hQ hV g,
    spin3Matrix_det Q hQ hV g⟩
  map_one' := Subtype.ext (map_one (spin3MatrixHom Q hQ hV))
  map_mul' g h := Subtype.ext (map_mul (spin3MatrixHom Q hQ hV) g h)

/-- The matrix underlying `spin3ToSL2` is the chosen even-Clifford matrix model. -/
@[simp]
theorem coe_spin3ToSL2_apply
    (hQ : Q.Nondegenerate) (hV : Module.finrank K V = 3) (g : spinGroup Q) :
    (spin3ToSL2 Q hQ hV g : Matrix (Fin 2) (Fin 2) K) =
      evenEquivMatrixTwoOfFinrankThree Q hQ hV (spinGroupToEven Q g) :=
  by
    rw [spin3ToSL2]
    exact spin3MatrixHom_apply Q hQ hV g

/-- The homomorphism `spin3ToSL2` is injective. -/
theorem spin3ToSL2_injective
    (hQ : Q.Nondegenerate) (hV : Module.finrank K V = 3) :
    Function.Injective (spin3ToSL2 Q hQ hV) := by
  intro g h hgh
  apply Subtype.ext
  have hm :
      evenEquivMatrixTwoOfFinrankThree Q hQ hV (spinGroupToEven Q g) =
        evenEquivMatrixTwoOfFinrankThree Q hQ hV (spinGroupToEven Q h) :=
    congrArg Subtype.val hgh
  have heven := (evenEquivMatrixTwoOfFinrankThree Q hQ hV).injective hm
  simpa only [coe_spinGroupToEven_apply] using
    congrArg (fun x : CliffordAlgebra.even Q ↦ (x : CliffordAlgebra Q)) heven

end TauCeti
