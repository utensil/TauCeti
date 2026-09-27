/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Equiv
public import TauCeti.Geometry.Diffeomorphism.Sphere
public import TauCeti.Topology.Homotopy.HomotopyGroup.HomotopyEquiv

/-!
# The Smale conjecture

The reference action of the orthogonal group on the round 3-sphere is already a continuous map
for the weak Whitney topology (`TauCeti.continuous_orthogonalToDiffSphere`).  This file packages
the resolved Smale conjecture in the precise form that the topology supports: the inclusion
`O(4) → Diff(S³)` is the forward map of a homotopy equivalence.  The homotopy equivalence itself
is recorded as a proposition, since this roadmap states the theorem rather than reproving
Hatcher's geometric argument.

The smoothness exponent is fixed at `∞`, and the sphere is the unit sphere in
`EuclideanSpace ℝ (Fin 4)`, so the source is the matrix orthogonal group `O(4)` and the target is
the self-diffeomorphism group of `S³` with its weak Whitney topology.

The formulation follows Hatcher's proof of the Smale conjecture and the statement requested in
`TauCetiRoadmap/GeometricTopology/README.md`, Layer 3.  No formalization is copied or vendored.

## Main declarations

* `TauCeti.smaleInclusion`: the continuous map `O(4) → Diff(S³)`.
* `TauCeti.SmaleConjecture`: the assertion that this map is a homotopy equivalence.
* `TauCeti.SmaleConjecture.exists_homotopyEquiv`: the homotopy-equivalence witness carried by the
  proposition.
* `TauCeti.SmaleConjecture.map_bijective`: the induced map on every finite-index homotopy group
  is bijective, conditional on the conjecture.
-/

public section

open Metric
open scoped Manifold ContDiff EuclideanSpace ContinuousMap
open scoped TauCeti.DiffeomorphWeakWhitney

namespace TauCeti

/-! The concrete source and target are written out in the public declarations below so that the
statement remains readable at call sites and follows the roadmap's `O(4)` / `Diff(S³)` notation.
-/

/-- The continuous reference inclusion `O(4) → Diff(S³)` used in the Smale statement. -/
noncomputable def smaleInclusion :
    C(Matrix.orthogonalGroup (Fin 4) ℝ,
      Diff (𝓡 3) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) ∞) :=
  ⟨orthogonalToDiffSphere 3 ∞, continuous_orthogonalToDiffSphere 3 ∞⟩

/-- The coercion from the bundled map recovers the orthogonal action. -/
@[simp]
theorem smaleInclusion_apply (A : Matrix.orthogonalGroup (Fin 4) ℝ) :
  smaleInclusion A = orthogonalToDiffSphere 3 ∞ A :=
  by
    -- The topology instance is intentionally opaque; this change exposes only the map coercion.
    change (orthogonalToDiffSphere 3 ∞) A = _
    rfl

/--
**The Smale conjecture**: the inclusion of the orthogonal group in the diffeomorphism group of the
round 3-sphere is a homotopy equivalence.

The equality in the existential makes the forward map canonical rather than merely asserting that
the two spaces happen to be homotopy equivalent.
-/
def SmaleConjecture : Prop :=
  ∃ e : Matrix.orthogonalGroup (Fin 4) ℝ ≃ₕ
      Diff (𝓡 3) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) ∞,
    e.toFun = smaleInclusion

namespace SmaleConjecture

/-! Elimination lemmas keep callers from unfolding the proposition and make its canonical-map
condition available as an ordinary equality of continuous maps.
-/

/-- A proof of the conjecture supplies a homotopy equivalence whose forward map is the inclusion. -/
theorem exists_homotopyEquiv (h : SmaleConjecture) :
    ∃ e : Matrix.orthogonalGroup (Fin 4) ℝ ≃ₕ
      Diff (𝓡 3) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) ∞,
      e.toFun = smaleInclusion :=
  h

/-- A proof of the conjecture makes the inclusion bijective on every finite-index homotopy group. -/
theorem map_bijective {N : Type*} [Finite N] (h : SmaleConjecture)
    (A : Matrix.orthogonalGroup (Fin 4) ℝ) :
    Function.Bijective (HomotopyGroup.map (N := N) smaleInclusion
      (rfl : smaleInclusion A = smaleInclusion A)) := by
  rcases h with ⟨e, he⟩
  rw [← he]
  exact HomotopyGroup.map_bijective_of_homotopyEquiv e A

end SmaleConjecture

end TauCeti
