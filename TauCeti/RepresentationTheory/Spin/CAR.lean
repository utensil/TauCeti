/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# The trace quadratic form for `gl_N`

The Layer 9 CAR worked instance uses the trace form on square complex matrices.

## Main definitions

* `TauCeti.traceQuadraticForm`: the quadratic form `X ↦ tr (X * X)` on `N × N` complex matrices.

## References

* [Clifford algebras, the Pin and Spin groups, and spin representations roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md),
  Layer 9, "The worked instance: `gl_N` on `M_N(ℂ)` (the CAR algebra)".
-/

public section

namespace TauCeti

/-- The trace quadratic form on `N × N` complex matrices. -/
noncomputable def traceQuadraticForm (N : ℕ) :
    QuadraticForm ℂ (Matrix (Fin N) (Fin N) ℂ) :=
  (Matrix.traceLinearMap (Fin N) ℂ ℂ).compQuadraticMap
    (QuadraticMap.sq (R := ℂ) (A := Matrix (Fin N) (Fin N) ℂ))

/-- The defining equation for `traceQuadraticForm`. -/
@[simp]
theorem traceQuadraticForm_apply (N : ℕ) (X : Matrix (Fin N) (Fin N) ℂ) :
    traceQuadraticForm N X = Matrix.trace (X * X) :=
  by simp [traceQuadraticForm]

end TauCeti
