/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Foliation.Basic

/-!
# Codimension-one foliations

This file records the codimension-one specialization of `TauCeti.Foliation`.  The generic
foliation structure already packages a smooth involutive distribution of a fixed rank; the
predicate below identifies the rank-one-codimension case needed by the foliation Euler-class
layer.  Leaves, transversals, and tautness are separate geometric data and are not folded into
this rank condition.
-/

public section

noncomputable section

open Module
open scoped Manifold ContDiff

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {k : ℕ}

namespace Foliation

variable [IsManifold I (n + 1) M]

/-- A foliation has codimension one when the rank of each leaf is one less than the
dimension of the model space. -/
def IsCodimensionOne (_F : Foliation I n M k) : Prop := k + 1 = finrank 𝕜 E

/-- The tangent distribution of a codimension-one foliation has the expected codimension. -/
theorem finrank_distribution_add_one (F : Foliation I n M k)
    (hF : F.IsCodimensionOne) (x : M) :
    finrank 𝕜 (F.distribution x) + 1 = finrank 𝕜 E := by
  rw [F.finrank_distribution]
  exact hF

variable [CompleteSpace 𝕜]

/-- A foliation by translates of a finite-dimensional subspace is codimension one exactly when
that subspace has codimension one in the ambient model space. -/
theorem ofSubmodule_isCodimensionOne (S : Submodule 𝕜 E) [FiniteDimensional 𝕜 S]
    (hn : 1 ≤ n) (hS : finrank 𝕜 S + 1 = finrank 𝕜 E) :
    (ofSubmodule S hn).IsCodimensionOne := by
  exact hS

end Foliation

end TauCeti
