/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.EvenEquiv

/-!
# Transporting even Clifford algebras along isometries

An isometry of quadratic spaces induces an algebra equivalence between their even Clifford
subalgebras. The equivalence is characterized on products of two Clifford generators.
-/

@[expose] public section


namespace CliffordAlgebra

variable {R M₁ M₂ : Type*} [CommRing R]
variable [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
variable {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}

/-- The algebra homomorphism on even Clifford algebras induced by an isometry. -/
noncomputable def evenMapOfIsometry (e : Q₁.IsometryEquiv Q₂) :
    CliffordAlgebra.even Q₁ →ₐ[R] CliffordAlgebra.even Q₂ :=
  even.lift Q₁
    { bilin := (even.ι Q₂).bilin.compl₁₂ e.toLinearEquiv.toLinearMap e.toLinearEquiv.toLinearMap
      contract := fun m => by
        rw [LinearMap.compl₁₂_apply, (even.ι Q₂).contract]
        exact congrArg (algebraMap R (CliffordAlgebra.even Q₂)) (e.map_app m)
      contract_mid := fun m₁ m₂ m₃ => by
        rw [LinearMap.compl₁₂_apply, LinearMap.compl₁₂_apply, (even.ι Q₂).contract_mid]
        exact congrArg (fun r => r • (even.ι Q₂).bilin (e m₁) (e m₃)) (e.map_app m₂) }

@[simp]
theorem evenMapOfIsometry_ι (e : Q₁.IsometryEquiv Q₂) (m₁ m₂ : M₁) :
    evenMapOfIsometry e ((even.ι Q₁).bilin m₁ m₂) =
      (even.ι Q₂).bilin (e m₁) (e m₂) := by
  rw [evenMapOfIsometry, even.lift_ι, LinearMap.compl₁₂_apply]
  rfl

/-- An isometry of quadratic spaces induces an algebra equivalence of their even Clifford
subalgebras. -/
noncomputable def evenEquivOfIsometry (e : Q₁.IsometryEquiv Q₂) :
    CliffordAlgebra.even Q₁ ≃ₐ[R] CliffordAlgebra.even Q₂ :=
  AlgEquiv.ofAlgHom (evenMapOfIsometry e) (evenMapOfIsometry e.symm)
    (by
      apply even.algHom_ext
      ext m₁ m₂
      simp)
    (by
      apply even.algHom_ext
      ext m₁ m₂
      simp)

@[simp]
theorem evenEquivOfIsometry_ι (e : Q₁.IsometryEquiv Q₂) (m₁ m₂ : M₁) :
    evenEquivOfIsometry e ((even.ι Q₁).bilin m₁ m₂) =
      (even.ι Q₂).bilin (e m₁) (e m₂) := by
  rw [evenEquivOfIsometry, AlgEquiv.ofAlgHom_apply, evenMapOfIsometry_ι]

end CliffordAlgebra
