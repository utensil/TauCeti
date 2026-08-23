/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.Clifford

/-!
# The left-regular CAR action

The normal-ordered quadratic lift of the general linear Lie algebra acts on its Clifford algebra by
left multiplication. The module instances are scoped to keep this action distinct from the ambient
commutator action on the Clifford algebra.

Activate the instances with `open scoped TauCeti`; consumers working with matrices also select the
usual associative-ring Lie bracket locally.

## Main results

* `TauCeti.carLieRingModule`: the left-regular CAR Lie-ring module.
* `TauCeti.carLieModule`: its linear Lie-module structure.
* `TauCeti.car_lie_def`: the defining left-multiplication equation.

## References

* [Tau Ceti Roadmap](https://github.com/TauCetiProject/TauCetiRoadmap), Representation Theory / Spin
  Representations, Layer 9, “The worked instance: `gl_N` on `M_N(ℂ)` (the CAR algebra)”.
-/

public section

namespace TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K n : Type*} [Field K] [Fintype n] [Invertible (2 : K)]

attribute [local instance] Classical.decEq
attribute [local instance] LieRingModule.ofAssociativeModule LieModule.ofAssociativeModule

/-- The left-regular CAR Lie-ring action transported along the normal-ordered quadratic lift. -/
noncomputable scoped instance carLieRingModule :
    LieRingModule (Matrix n n K) (CliffordAlgebra (traceQuadraticForm K n)) :=
  LieRingModule.compLieHom _ (glCliffordHom (K := K) (n := n))

attribute [local instance] carLieRingModule

/-- The left-regular CAR action is linear over the coefficient field. -/
noncomputable scoped instance carLieModule :
    LieModule K (Matrix n n K) (CliffordAlgebra (traceQuadraticForm K n)) :=
  LieModule.compLieHom _ (glCliffordHom (K := K) (n := n))

attribute [local instance] carLieModule

/-- The CAR Lie action is left multiplication by the normal-ordered quadratic lift. -/
@[simp, grind =]
theorem car_lie_def (X : Matrix n n K) (c : CliffordAlgebra (traceQuadraticForm K n)) :
    ⁅X, c⁆ = glCliffordHom (K := K) (n := n) X * c := by
  rfl

end TauCeti
