/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.RealForm

import Mathlib.LinearAlgebra.CliffordAlgebra.Prod
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Quaternion recurrence for Clifford algebras

Adjoining two generators of square `-1` changes the sign of a quadratic form and tensors its
Clifford algebra with a quaternion algebra. The standard real specialization supplies the
complementary recurrence used in eightfold periodicity.

## Main results

* `quaternionEquivTensor` adjoins the quaternion plane to an arbitrary quadratic form.
* `realCliffordQuaternionSplitIsometry` supplies the standard form-preserving coordinate split.
* `realCliffordQuaternionRecurrenceEquiv` gives the standard real recurrence.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry*, Chapter I.
* [TauCeti SpinRepresentations roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SpinRepresentations/Suggested.lean)
-/

public section

open Module QuadraticMap
open scoped Quaternion TensorProduct
namespace TauCeti.CliffordAlgebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M)

private abbrev H := ℍ[R,(-1),(-1)]
private def qK : H (R := R) := ⟨0, 0, 0, 1⟩
private def qPure (v : R × R) : H (R := R) := ⟨0, v.1, v.2, 0⟩

private theorem qK_sq : qK (R := R) * qK = -1 := by
  simpa [qK] using (QuaternionAlgebra.Basis.k_mul_k
    (QuaternionAlgebra.Basis.self R (c₁ := (-1 : R)) (c₂ := 0) (c₃ := -1)))

private theorem qPure_sq (v : R × R) : qPure v * qPure v =
    algebraMap R (H (R := R)) (CliffordAlgebraQuaternion.Q (-1) (-1) v) := by
  simp only [qPure]
  rw [← CliffordAlgebraQuaternion.toQuaternion_ι v, ← map_mul,
    _root_.CliffordAlgebra.ι_sq_scalar]
  exact (CliffordAlgebraQuaternion.toQuaternion
    (R := R) (c₁ := (-1 : R)) (c₂ := -1)).commutes _

private theorem qK_anticomm_qPure (v : R × R) :
    qK (R := R) * qPure v + qPure v * qK = 0 := by
  let b := QuaternionAlgebra.Basis.self R
    (c₁ := (-1 : R)) (c₂ := 0) (c₃ := -1)
  have hk : qK (R := R) = b.k := by ext <;> simp [qK, b]
  have hv : qPure v = v.1 • b.i + v.2 • b.j := by ext <;> simp [qPure, b]
  rw [hk, hv]
  simp [mul_add, add_mul]
  abel

private def baseGen : M →ₗ[R] (_root_.CliffordAlgebra (-Q) ⊗[R] H (R := R)) :=
  ((TensorProduct.mk R _ _).flip (qK (R := R))).comp (_root_.CliffordAlgebra.ι (-Q))

private def planeGen : (R × R) →ₗ[R] (_root_.CliffordAlgebra (-Q) ⊗[R] H (R := R)) :=
  (Algebra.TensorProduct.includeRight : H (R := R) →ₐ[R] _).toLinearMap.comp
    ((CliffordAlgebraQuaternion.equiv : _ ≃ₐ[R] H (R := R)).toLinearMap.comp
      (_root_.CliffordAlgebra.ι (CliffordAlgebraQuaternion.Q (-1 : R) (-1))))

private def generator : M × (R × R) →ₗ[R]
    (_root_.CliffordAlgebra (-Q) ⊗[R] H (R := R)) :=
  (baseGen Q).coprod (planeGen Q)

private theorem generator_apply (x : M × (R × R)) :
    generator Q x =
      _root_.CliffordAlgebra.ι (-Q) x.1 ⊗ₜ[R] qK + 1 ⊗ₜ[R] qPure x.2 := by
  simp only [generator, LinearMap.coprod_apply, baseGen, planeGen,
    LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply,
    AlgHom.toLinearMap_apply, Algebra.TensorProduct.includeRight_apply]
  congr 2
  -- The plane generator is a composition of three bundled maps; expose its final application.
  change CliffordAlgebraQuaternion.equiv
      (_root_.CliffordAlgebra.ι (CliffordAlgebraQuaternion.Q (-1 : R) (-1)) x.2) = _
  rw [CliffordAlgebraQuaternion.equiv_apply, CliffordAlgebraQuaternion.toQuaternion_ι]
  rfl

private abbrev PlaneQ : QuadraticForm R (R × R) :=
  CliffordAlgebraQuaternion.Q (-1 : R) (-1)

private abbrev Source := _root_.CliffordAlgebra (Q.prod (PlaneQ (R := R)))

private def eI : Source Q :=
  _root_.CliffordAlgebra.ι _ (0, (1, 0))

private def eJ : Source Q :=
  _root_.CliffordAlgebra.ι _ (0, (0, 1))

private def volume : Source Q := eI Q * eJ Q

private theorem eI_sq : eI Q * eI Q = -1 := by
  rw [eI, _root_.CliffordAlgebra.ι_sq_scalar]
  simp [PlaneQ, QuadraticMap.prod_apply]

private theorem eJ_sq : eJ Q * eJ Q = -1 := by
  rw [eJ, _root_.CliffordAlgebra.ι_sq_scalar]
  simp [PlaneQ, QuadraticMap.prod_apply]

private theorem eJ_mul_eI : eJ Q * eI Q = -(eI Q * eJ Q) := by
  rw [eq_neg_iff_add_eq_zero]
  simpa [eI, eJ, PlaneQ, QuadraticMap.polar] using
    (_root_.CliffordAlgebra.ι_mul_ι_add_swap
      (Q := Q.prod (PlaneQ (R := R))) (0, (0, 1)) (0, (1, 0)))

private theorem volume_sq : volume Q * volume Q = -1 := by
  rw [volume, mul_assoc, ← mul_assoc (eJ Q) (eI Q) (eJ Q), eJ_mul_eI]
  simp only [mul_neg, neg_mul, mul_assoc]
  rw [← mul_assoc (eI Q) (eI Q) (eJ Q * eJ Q), eI_sq, eJ_sq]
  simp

private theorem base_comm_volume (m : M) :
    Commute (_root_.CliffordAlgebra.ι _ (m, 0)) (volume Q) := by
  simpa [volume, eI, eJ] using
    (_root_.CliffordAlgebra.commute_map_mul_map_of_isOrtho_of_mem_evenOdd_zero_right
      (f₁ := QuadraticMap.Isometry.inl Q (PlaneQ (R := R)))
      (f₂ := QuadraticMap.Isometry.inr Q (PlaneQ (R := R)))
      (hf := fun _ _ ↦ QuadraticMap.IsOrtho.inl_inr _ _)
      (_root_.CliffordAlgebra.ι Q m)
      (_root_.CliffordAlgebra.ι (PlaneQ (R := R)) (1, 0) *
        _root_.CliffordAlgebra.ι (PlaneQ (R := R)) (0, 1))
      (_root_.CliffordAlgebra.ι_mem_evenOdd_one Q m)
      (_root_.CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero (PlaneQ (R := R)) (1, 0) (0, 1)))

private def inverseBaseGenerator : M →ₗ[R] Source Q :=
  -(LinearMap.mulRight R (volume Q)).comp
    ((_root_.CliffordAlgebra.ι _).comp (LinearMap.inl R M (R × R)))

private theorem inverseBaseGenerator_apply (m : M) :
    inverseBaseGenerator Q m = -(_root_.CliffordAlgebra.ι _ (m, 0) * volume Q) := by
  rfl

private theorem inverseBaseGenerator_sq (m : M) :
    inverseBaseGenerator Q m * inverseBaseGenerator Q m =
      algebraMap R _ ((-Q) m) := by
  rw [inverseBaseGenerator_apply, neg_mul_neg]
  rw [← pow_two, (base_comm_volume Q m).mul_pow, pow_two, pow_two,
    _root_.CliffordAlgebra.ι_sq_scalar, volume_sq]
  simp

private def inverseBaseInclusion :
    _root_.CliffordAlgebra (-Q) →ₐ[R] Source Q :=
  _root_.CliffordAlgebra.lift (-Q)
    ⟨inverseBaseGenerator Q, inverseBaseGenerator_sq Q⟩

private theorem inverseBaseInclusion_ι (m : M) :
    inverseBaseInclusion Q (_root_.CliffordAlgebra.ι (-Q) m) =
      -(_root_.CliffordAlgebra.ι _ (m, 0) * volume Q) := by
  rw [inverseBaseInclusion, _root_.CliffordAlgebra.lift_ι_apply,
    inverseBaseGenerator_apply]

private def planeRightInclusion :
    _root_.CliffordAlgebra (PlaneQ (R := R)) →ₐ[R] Source Q :=
  _root_.CliffordAlgebra.map (QuadraticMap.Isometry.inr Q (PlaneQ (R := R)))

private noncomputable def quaternionInclusion : H (R := R) →ₐ[R] Source Q :=
  (planeRightInclusion Q).comp
    (CliffordAlgebraQuaternion.equiv :
      _root_.CliffordAlgebra (PlaneQ (R := R)) ≃ₐ[R] H (R := R)).symm.toAlgHom

private theorem quaternionInclusion_qPure (v : R × R) :
    quaternionInclusion Q (qPure v) =
      _root_.CliffordAlgebra.ι _ (0, v) := by
  rw [quaternionInclusion, AlgHom.comp_apply]
  -- Expose the inverse quaternion equivalence inside the composed inclusion.
  change planeRightInclusion Q
    ((CliffordAlgebraQuaternion.equiv :
      _root_.CliffordAlgebra (PlaneQ (R := R)) ≃ₐ[R] H (R := R)).symm (qPure v)) = _
  have hpure : qPure v = CliffordAlgebraQuaternion.equiv
      (_root_.CliffordAlgebra.ι (PlaneQ (R := R)) v) := by
    rw [CliffordAlgebraQuaternion.equiv_apply, CliffordAlgebraQuaternion.toQuaternion_ι]
    rfl
  rw [hpure, AlgEquiv.symm_apply_apply]
  simp [planeRightInclusion]

private theorem quaternionInclusion_qK :
    quaternionInclusion Q (qK (R := R)) = volume Q := by
  have hk : qK (R := R) = qPure ((1 : R), 0) * qPure (0, 1) := by
    simp [qK, qPure]
  rw [hk]
  rw [map_mul, quaternionInclusion_qPure, quaternionInclusion_qPure]
  rfl

private theorem quaternionInclusion_mk (a b c d : R) :
    quaternionInclusion Q (⟨a, b, c, d⟩ : H (R := R)) =
      algebraMap R _ a + b • eI Q + c • eJ Q + d • volume Q := by
  rw [quaternionInclusion, AlgHom.comp_apply]
  -- Expose the inverse quaternion equivalence before using its named coordinate equation.
  change planeRightInclusion Q
    (CliffordAlgebraQuaternion.ofQuaternion (⟨a, b, c, d⟩ : H (R := R))) = _
  rw [CliffordAlgebraQuaternion.ofQuaternion_mk, map_add, map_add, map_add,
    map_smul, map_smul, map_smul, map_mul]
  simp [planeRightInclusion, eI, eJ, volume]

private theorem baseGenerator_comm_plane (m : M) (v : R × R) :
    Commute (inverseBaseGenerator Q m) (_root_.CliffordAlgebra.ι _ (0, v)) := by
  let b := _root_.CliffordAlgebra.ι (Q.prod (PlaneQ (R := R))) (m, 0)
  let e := _root_.CliffordAlgebra.ι (Q.prod (PlaneQ (R := R))) (0, v)
  have hbe : b * e = -(e * b) :=
    _root_.CliffordAlgebra.ι_mul_ι_comm_of_isOrtho
      (QuadraticMap.IsOrtho.inl_inr (Q₁ := Q) (Q₂ := PlaneQ (R := R)) m v)
  have hve : volume Q * e = -(e * volume Q) := by
    have h := congrArg (quaternionInclusion Q) (qK_anticomm_qPure (R := R) v)
    simpa only [map_add, map_mul, map_zero, quaternionInclusion_qK,
      quaternionInclusion_qPure, eq_neg_iff_add_eq_zero] using h
  rw [Commute, inverseBaseGenerator_apply]
  -- `b` and `e` name the two Clifford generators hidden by the bundled linear map.
  change -(b * volume Q) * e = e * -(b * volume Q)
  calc
    -(b * volume Q) * e = -(b * (volume Q * e)) := by simp [mul_assoc]
    _ = -(b * (-(e * volume Q))) := by rw [hve]
    _ = b * (e * volume Q) := by simp
    _ = (b * e) * volume Q := by simp [mul_assoc]
    _ = (-(e * b)) * volume Q := by rw [hbe]
    _ = e * -(b * volume Q) := by simp [mul_assoc]

private theorem baseGenerator_comm_volume (m : M) :
    Commute (inverseBaseGenerator Q m) (volume Q) := by
  rw [inverseBaseGenerator_apply]
  -- Expose the right-multiplication map so the recorded commutation equation applies.
  change -(_root_.CliffordAlgebra.ι _ (m, 0) * volume Q) * volume Q =
    volume Q * -(_root_.CliffordAlgebra.ι _ (m, 0) * volume Q)
  have h := base_comm_volume Q m
  rw [Commute] at h
  rw [neg_mul, mul_neg]
  congr 1
  rw [← mul_assoc (volume Q) (_root_.CliffordAlgebra.ι _ (m, 0)) (volume Q), h]

private theorem inverseBaseGenerator_comm_quaternion (m : M) (y : H (R := R)) :
    Commute (inverseBaseGenerator Q m) (quaternionInclusion Q y) := by
  rw [← QuaternionAlgebra.mk.eta y, quaternionInclusion_mk]
  have hr : Commute (inverseBaseGenerator Q m) (algebraMap R _ y.re) :=
    (Algebra.commutes y.re _).symm
  exact (((hr.add_right
      ((baseGenerator_comm_plane Q m (1, 0)).smul_right y.imI)).add_right
        ((baseGenerator_comm_plane Q m (0, 1)).smul_right y.imJ)).add_right
      ((baseGenerator_comm_volume Q m).smul_right y.imK))

private theorem inverseBaseInclusion_comm_quaternionInclusion
    (x : _root_.CliffordAlgebra (-Q)) (y : H (R := R)) :
    Commute (inverseBaseInclusion Q x) (quaternionInclusion Q y) := by
  induction x using _root_.CliffordAlgebra.induction with
  | algebraMap r =>
      rw [(inverseBaseInclusion Q).commutes]
      exact Algebra.commutes r _
  | ι m =>
      rw [inverseBaseInclusion_ι]
      exact inverseBaseGenerator_comm_quaternion Q m y
  | mul a b ha hb => simpa only [map_mul] using ha.mul_left hb
  | add a b ha hb => simpa only [map_add] using ha.add_left hb

private noncomputable def fromTensor :
    (_root_.CliffordAlgebra (-Q) ⊗[R] H (R := R)) →ₐ[R] Source Q :=
  Algebra.TensorProduct.lift (inverseBaseInclusion Q) (quaternionInclusion Q)
    (inverseBaseInclusion_comm_quaternionInclusion Q)

private def toTensor :
    Source Q →ₐ[R] (_root_.CliffordAlgebra (-Q) ⊗[R] H (R := R)) :=
  _root_.CliffordAlgebra.lift _ ⟨generator Q, by
    intro x
    rw [generator_apply]
    rw [add_mul, mul_add, mul_add]
    simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one,
      _root_.CliffordAlgebra.ι_sq_scalar]
    rw [qK_sq, qPure_sq]
    -- Regroup the two mixed tensors before applying the named anticommutation identity.
    rw [show
        (algebraMap R (_root_.CliffordAlgebra (-Q)) ((-Q) x.1) ⊗ₜ[R] (-1)) +
            (_root_.CliffordAlgebra.ι (-Q) x.1 ⊗ₜ[R] (qK * qPure x.2)) +
            ((_root_.CliffordAlgebra.ι (-Q) x.1 ⊗ₜ[R] (qPure x.2 * qK)) +
              1 ⊗ₜ[R] algebraMap R (H (R := R)) (PlaneQ (R := R) x.2)) =
          (algebraMap R (_root_.CliffordAlgebra (-Q)) ((-Q) x.1) ⊗ₜ[R] (-1)) +
            (_root_.CliffordAlgebra.ι (-Q) x.1 ⊗ₜ[R]
              (qK * qPure x.2 + qPure x.2 * qK)) +
            1 ⊗ₜ[R] algebraMap R (H (R := R)) (PlaneQ (R := R) x.2) by
        rw [TensorProduct.tmul_add]
        abel,
      qK_anticomm_qPure, TensorProduct.tmul_zero, add_zero]
    rw [QuadraticMap.prod_apply]
    simp only [neg_apply, map_add, map_neg]
    -- The two minus signs may move between tensor factors only through tensor bilinearity.
    rw [show (-(algebraMap R (_root_.CliffordAlgebra (-Q)) (Q x.1))) ⊗ₜ[R]
          (-1 : H (R := R)) =
        algebraMap R (_root_.CliffordAlgebra (-Q)) (Q x.1) ⊗ₜ[R] 1 by
      simp only [TensorProduct.neg_tmul, TensorProduct.tmul_neg, neg_neg]]
    rw [← Algebra.TensorProduct.tmul_one_eq_one_tmul,
      Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply]⟩

private theorem toTensor_ι (x : M × (R × R)) :
    toTensor Q (_root_.CliffordAlgebra.ι _ x) =
      _root_.CliffordAlgebra.ι (-Q) x.1 ⊗ₜ[R] qK + 1 ⊗ₜ[R] qPure x.2 := by
  rw [toTensor, _root_.CliffordAlgebra.lift_ι_apply]
  exact generator_apply Q x

private theorem toTensor_volume : toTensor Q (volume Q) = 1 ⊗ₜ[R] qK := by
  rw [volume, eI, eJ, map_mul]
  rw [toTensor_ι, toTensor_ι]
  simp only [map_zero, TensorProduct.zero_tmul, zero_add]
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, qK]
  congr 1
  apply QuaternionAlgebra.ext
  · rw [QuaternionAlgebra.re_mul]; simp [qPure]
  · rw [QuaternionAlgebra.imI_mul]; simp [qPure]
  · rw [QuaternionAlgebra.imJ_mul]; simp [qPure]
  · rw [QuaternionAlgebra.imK_mul]; simp [qPure]

private theorem fromTensor_base (m : M) :
    fromTensor Q (_root_.CliffordAlgebra.ι (-Q) m ⊗ₜ[R] qK) =
      _root_.CliffordAlgebra.ι _ (m, 0) := by
  rw [fromTensor, Algebra.TensorProduct.lift_tmul, inverseBaseInclusion_ι,
    quaternionInclusion_qK]
  rw [neg_mul, mul_assoc, volume_sq]
  simp

private theorem fromTensor_plane (v : R × R) :
    fromTensor Q (1 ⊗ₜ[R] qPure v) =
      _root_.CliffordAlgebra.ι _ (0, v) := by
  rw [fromTensor, Algebra.TensorProduct.lift_tmul, map_one, one_mul,
    quaternionInclusion_qPure]

private theorem fromTensor_comp_toTensor :
    (fromTensor Q).comp (toTensor Q) = AlgHom.id R _ := by
  apply _root_.CliffordAlgebra.hom_ext
  apply LinearMap.ext
  rintro ⟨m, v⟩
  -- The composite algebra homomorphism has no application lemma beyond its two constituent maps.
  change fromTensor Q (toTensor Q (_root_.CliffordAlgebra.ι _ (m, v))) =
    _root_.CliffordAlgebra.ι _ (m, v)
  rw [toTensor_ι, map_add, fromTensor_base, fromTensor_plane]
  rw [← map_add]
  congr 2
  ext <;> simp

private theorem toTensor_inverseBaseInclusion_ι (m : M) :
    toTensor Q (inverseBaseInclusion Q (_root_.CliffordAlgebra.ι (-Q) m)) =
      _root_.CliffordAlgebra.ι (-Q) m ⊗ₜ[R] 1 := by
  rw [inverseBaseInclusion_ι, map_neg, map_mul, toTensor_ι, toTensor_volume]
  have hzero : qPure (0 : R × R) = 0 := by rfl
  rw [hzero, TensorProduct.tmul_zero, add_zero,
    Algebra.TensorProduct.tmul_mul_tmul,
    qK_sq]
  simp only [mul_one, TensorProduct.tmul_neg, neg_neg]

private theorem toTensor_comp_inverseBaseInclusion :
    (toTensor Q).comp (inverseBaseInclusion Q) =
      (Algebra.TensorProduct.includeLeft :
        _root_.CliffordAlgebra (-Q) →ₐ[R]
          (_root_.CliffordAlgebra (-Q) ⊗[R] H (R := R))) := by
  apply _root_.CliffordAlgebra.hom_ext
  ext m
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply,
    toTensor_inverseBaseInclusion_ι, Algebra.TensorProduct.includeLeft_apply]

private theorem quaternionInclusion_comp_equiv :
    (quaternionInclusion Q).comp
        (CliffordAlgebraQuaternion.equiv :
          _root_.CliffordAlgebra (PlaneQ (R := R)) ≃ₐ[R] H (R := R)).toAlgHom =
      planeRightInclusion Q := by
  rw [quaternionInclusion, AlgHom.comp_assoc]
  simp

private theorem toTensor_comp_quaternionInclusion :
    (toTensor Q).comp (quaternionInclusion Q) =
      (Algebra.TensorProduct.includeRight :
        H (R := R) →ₐ[R] (_root_.CliffordAlgebra (-Q) ⊗[R] H (R := R))) := by
  apply (AlgHom.cancel_right (R := R)
    (f := (CliffordAlgebraQuaternion.equiv :
      _root_.CliffordAlgebra (PlaneQ (R := R)) ≃ₐ[R] H (R := R)).toAlgHom)
    (CliffordAlgebraQuaternion.equiv :
      _root_.CliffordAlgebra (PlaneQ (R := R)) ≃ₐ[R] H (R := R)).surjective).mp
  rw [AlgHom.comp_assoc, quaternionInclusion_comp_equiv]
  apply _root_.CliffordAlgebra.hom_ext
  apply LinearMap.ext
  intro v
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply,
    planeRightInclusion, _root_.CliffordAlgebra.map_apply_ι,
    QuadraticMap.Isometry.inr_apply, toTensor_ι, map_zero,
    TensorProduct.zero_tmul, zero_add, Algebra.TensorProduct.includeRight_apply]
  -- The tensor factor contains the bundled quaternion equivalence, whose generator equation is
  -- stated for the equivalence application rather than the surrounding pure tensor.
  change 1 ⊗ₜ[R] qPure v = 1 ⊗ₜ[R] CliffordAlgebraQuaternion.equiv
    (_root_.CliffordAlgebra.ι (PlaneQ (R := R)) v)
  rw [CliffordAlgebraQuaternion.equiv_apply, CliffordAlgebraQuaternion.toQuaternion_ι]
  rfl

private theorem toTensor_comp_fromTensor :
    (toTensor Q).comp (fromTensor Q) = AlgHom.id R _ := by
  apply AlgHom.toLinearMap_injective
  apply TensorProduct.ext'
  intro x y
  simp only [AlgHom.toLinearMap_apply, AlgHom.comp_apply, fromTensor,
    Algebra.TensorProduct.lift_tmul, map_mul, AlgHom.id_apply]
  have hx : toTensor Q (inverseBaseInclusion Q x) = x ⊗ₜ[R] 1 := by
    simpa only [AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply] using
      DFunLike.congr_fun (toTensor_comp_inverseBaseInclusion Q) x
  have hy : toTensor Q (quaternionInclusion Q y) = 1 ⊗ₜ[R] y := by
    simpa only [AlgHom.comp_apply, Algebra.TensorProduct.includeRight_apply] using
      DFunLike.congr_fun (toTensor_comp_quaternionInclusion Q) y
  rw [hx, hy]
  simp

/-- Adjoining the quaternion plane `⟨-1,-1⟩` changes the sign of a quadratic form and
tensors its Clifford algebra with the corresponding quaternion algebra. -/
noncomputable def quaternionEquivTensor :
    _root_.CliffordAlgebra
        (Q.prod (CliffordAlgebraQuaternion.Q (-1 : R) (-1))) ≃ₐ[R]
      _root_.CliffordAlgebra (-Q) ⊗[R] ℍ[R,(-1),(-1)] :=
  AlgEquiv.ofAlgHom (toTensor Q) (fromTensor Q)
    (toTensor_comp_fromTensor Q) (fromTensor_comp_toTensor Q)

/-- `quaternionEquivTensor` on the Clifford generator of the product quadratic form. -/
@[simp]
theorem quaternionEquivTensor_ι (x : M × (R × R)) :
    quaternionEquivTensor Q (_root_.CliffordAlgebra.ι _ x) =
      _root_.CliffordAlgebra.ι (-Q) x.1 ⊗ₜ[R]
          (⟨0, 0, 0, 1⟩ : ℍ[R,(-1),(-1)]) +
        1 ⊗ₜ[R] (⟨0, x.2.1, x.2.2, 0⟩ : ℍ[R,(-1),(-1)]) := by
  rw [quaternionEquivTensor, AlgEquiv.ofAlgHom_apply, toTensor_ι]
  rfl

/-- The inverse of `quaternionEquivTensor` on a generator from the sign-reversed base. -/
@[simp]
theorem quaternionEquivTensor_symm_apply_ι_base (m : M) :
    (quaternionEquivTensor Q).symm
        (_root_.CliffordAlgebra.ι (-Q) m ⊗ₜ[R]
          (⟨0, 0, 0, 1⟩ : ℍ[R,(-1),(-1)])) =
      _root_.CliffordAlgebra.ι _ (m, (0 : R × R)) := by
  apply (quaternionEquivTensor Q).injective
  rw [AlgEquiv.apply_symm_apply, quaternionEquivTensor_ι]
  -- Normalize the explicit zero quaternion before tensor simplification.
  change _ = _ + 1 ⊗ₜ[R] (0 : ℍ[R,(-1),(-1)])
  simp

/-- The inverse of `quaternionEquivTensor` on a generator from the quaternion plane. -/
@[simp]
theorem quaternionEquivTensor_symm_apply_ι_plane (v : R × R) :
    (quaternionEquivTensor Q).symm
        (1 ⊗ₜ[R] (⟨0, v.1, v.2, 0⟩ : ℍ[R,(-1),(-1)])) =
      _root_.CliffordAlgebra.ι _ (0, v) := by
  apply (quaternionEquivTensor Q).injective
  rw [AlgEquiv.apply_symm_apply]
  simp

end TauCeti.CliffordAlgebra

namespace TauCeti

/-- Splits the standard signature `(p,q+2)` into the sign-reversed `(q,p)` form and the
two-generator quaternion form. -/
def realCliffordQuaternionSplitIsometry (p q : ℕ) :
    (realCliffordForm p (q + 2)).IsometryEquiv
      ((-realCliffordForm q p).prod (CliffordAlgebraQuaternion.Q (-1 : ℝ) (-1))) :=
  (realCliffordSplitIsometry p 0 q 2).trans <|
    (realCliffordFormNegIsometry q p).symm.prod realCliffordZeroTwoIsometry

/-- The quaternion splitter is the shared signature splitter followed by the standard
sign-reversal and `(0,2)` coordinate isometries. -/
@[simp]
theorem realCliffordQuaternionSplitIsometry_apply (p q : ℕ)
    (x : Fin (p + (q + 2)) → ℝ) :
    realCliffordQuaternionSplitIsometry p q x =
      ((realCliffordFormNegIsometry q p).symm
          (realCliffordSplitIsometry p 0 q 2 x).1,
        realCliffordZeroTwoIsometry (realCliffordSplitIsometry p 0 q 2 x).2) := by
  rw [realCliffordQuaternionSplitIsometry]
  -- `IsometryEquiv.trans` and `IsometryEquiv.prod` expose their application only through the
  -- underlying bundled linear equivalences.
  change ((realCliffordFormNegIsometry q p).symm
      (realCliffordSplitIsometry p 0 q 2 x).1,
    realCliffordZeroTwoIsometry (realCliffordSplitIsometry p 0 q 2 x).2) = _
  rfl

private def negNegIsometry (Q : QuadraticForm ℝ (Fin (q + p) → ℝ)) :
    (-(-Q)).IsometryEquiv Q :=
  { LinearEquiv.refl ℝ _ with map_app' := by simp }

private noncomputable def realQuaternionTargetEquiv (p q : ℕ) :
    _root_.CliffordAlgebra (-(-realCliffordForm q p)) ⊗[ℝ] ℍ[ℝ,(-1),(-1)] ≃ₐ[ℝ]
      _root_.CliffordAlgebra (realCliffordForm q p) ⊗[ℝ] ℍ[ℝ] :=
  Algebra.TensorProduct.congr
    (_root_.CliffordAlgebra.equivOfIsometry (negNegIsometry (p := p) (q := q)
      (realCliffordForm q p)))
    (AlgEquiv.refl : ℍ[ℝ,(-1),(-1)] ≃ₐ[ℝ] ℍ[ℝ])

private theorem realQuaternionTargetEquiv_tmul (p q : ℕ)
    (a : _root_.CliffordAlgebra (-(-realCliffordForm q p)))
    (b : ℍ[ℝ,(-1),(-1)]) :
    realQuaternionTargetEquiv p q (a ⊗ₜ[ℝ] b) =
      _root_.CliffordAlgebra.equivOfIsometry
          (negNegIsometry (p := p) (q := q) (realCliffordForm q p)) a ⊗ₜ[ℝ]
        b := rfl

/-- The quaternion recurrence for the standard real Clifford algebras. -/
noncomputable def realCliffordQuaternionRecurrenceEquiv (p q : ℕ) :
    _root_.CliffordAlgebra (realCliffordForm p (q + 2)) ≃ₐ[ℝ]
      _root_.CliffordAlgebra (realCliffordForm q p) ⊗[ℝ] ℍ[ℝ] :=
  (_root_.CliffordAlgebra.equivOfIsometry
      (realCliffordQuaternionSplitIsometry p q)).trans <|
    (CliffordAlgebra.quaternionEquivTensor (-realCliffordForm q p)).trans <|
      realQuaternionTargetEquiv p q

private theorem realCliffordQuaternionRecurrenceEquiv_eq (p q : ℕ)
    (x : _root_.CliffordAlgebra (realCliffordForm p (q + 2))) :
    realCliffordQuaternionRecurrenceEquiv p q x =
      realQuaternionTargetEquiv p q
        (CliffordAlgebra.quaternionEquivTensor (-realCliffordForm q p)
          (_root_.CliffordAlgebra.equivOfIsometry
            (realCliffordQuaternionSplitIsometry p q) x)) := rfl

/-- `realCliffordQuaternionRecurrenceEquiv` on a standard Clifford generator. -/
@[simp]
theorem realCliffordQuaternionRecurrenceEquiv_ι (p q : ℕ)
    (x : Fin (p + (q + 2)) → ℝ) :
    realCliffordQuaternionRecurrenceEquiv p q
        (_root_.CliffordAlgebra.ι (realCliffordForm p (q + 2)) x) =
      _root_.CliffordAlgebra.ι (realCliffordForm q p)
          (realCliffordQuaternionSplitIsometry p q x).1 ⊗ₜ[ℝ]
            (⟨0, 0, 0, 1⟩ : ℍ[ℝ]) +
        1 ⊗ₜ[ℝ] (⟨0, (realCliffordQuaternionSplitIsometry p q x).2.1,
          (realCliffordQuaternionSplitIsometry p q x).2.2, 0⟩ : ℍ[ℝ]) := by
  rw [realCliffordQuaternionRecurrenceEquiv_eq,
    _root_.CliffordAlgebra.equivOfIsometry_apply,
    _root_.CliffordAlgebra.map_apply_ι,
    CliffordAlgebra.quaternionEquivTensor_ι, map_add,
    realQuaternionTargetEquiv_tmul, realQuaternionTargetEquiv_tmul, map_one]
  rw [_root_.CliffordAlgebra.equivOfIsometry_apply,
    _root_.CliffordAlgebra.map_apply_ι]
  rfl

end TauCeti
