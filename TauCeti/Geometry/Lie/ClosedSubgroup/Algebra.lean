/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Lie.Exponential.Basic
public import TauCeti.Geometry.Lie.Interior
import TauCeti.Geometry.Lie.Adjoint.Infinitesimal
import TauCeti.Geometry.Lie.Exponential.Trotter

/-!
# The Lie algebra of a closed subgroup

For a closed subgroup `K` of a finite-dimensional Lie group, the tangent vectors whose complete
exponential lines lie in `K` form a Lie subalgebra. Addition follows from the Trotter product
formula; bracket closure follows by differentiating the adjoint orbit inside the same closed
subspace.

## Main results

* `lieSubalgebraOfClosedSubgroup`: the Lie subalgebra cut out by exponential lines in `K`.
* `mem_lieSubalgebraOfClosedSubgroup_iff`: its characteristic membership equation.

## References

* [H. Liu, *Notes for Lie Groups & Representations*](https://member.ipmu.jp/henry.liu/notes/f16-lie-groups.pdf),
  notes from Andrei Okounkov's Fall 2016 course, Section 2.4.
* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 2, "The Lie subalgebra of a subgroup".
-/

public section

noncomputable section

namespace TauCeti.Lie

open Filter Manifold
open scoped ContDiff Manifold Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [IsManifold I 1 G] [LieGroup I ∞ G]

attribute [local instance] LieGroup.minSmoothnessThree
attribute [local instance] ContMDiffMul.boundarylessManifold

private def closedSubgroupTangentSubmodule (K : Subgroup G) (hK : IsClosed (K : Set G)) :
    Submodule ℝ (GroupLieAlgebra I G) := by
  let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
  exact
    { carrier := {X | ∀ t : ℝ, mulInvariantExp (I := I) (G := G) (t • X) ∈ K}
      zero_mem' := by
        intro t
        simp only [smul_zero, mulInvariantExp_zero, K.one_mem]
      add_mem' := by
        intro X Y hX hY t
        apply hK.mem_of_tendsto
          (tendsto_mulInvariantExp_smul_mul_mulInvariantExp_smul_pow
            (I := I) (G := G) X Y t)
        exact Eventually.of_forall fun n => K.pow_mem (K.mul_mem (hX _) (hY _)) n
      smul_mem' := by
        intro c X hX t
        simpa only [smul_smul] using hX (t * c) }

private theorem tangentAd_mem_closedSubgroupTangentSubmodule
    (K : Subgroup G) (hK : IsClosed (K : Set G))
    {X : GroupLieAlgebra I G}
    (hX : X ∈ closedSubgroupTangentSubmodule (I := I) K hK)
    (g : K) :
    tangentAd (I := I) (g : G) X ∈ closedSubgroupTangentSubmodule (I := I) K hK := by
  intro t
  let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
  have hconj := conj_mulInvariantExp (I := I) (g : G) (t • X)
  have hconj' :
      (g : G) * mulInvariantExp (I := I) (G := G) (t • X) * (g : G)⁻¹ =
        mulInvariantExp (I := I) (G := G) (t • tangentAd (I := I) (g : G) X) := by
    simpa only [map_smul] using hconj
  rw [← hconj']
  exact K.mul_mem (K.mul_mem g.property (hX t)) (K.inv_mem g.property)

private def closedSubgroupTangentLieSubalgebra
    (K : Subgroup G) (hK : IsClosed (K : Set G)) :
    LieSubalgebra ℝ (GroupLieAlgebra I G) := by
  let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
  let _ : T2Space (GroupLieAlgebra I G) := inferInstanceAs (T2Space E)
  let _ : FiniteDimensional ℝ (GroupLieAlgebra I G) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  exact
    { __ := closedSubgroupTangentSubmodule (I := I) K hK
      lie_mem' := by
        intro X Y hX hY
        let M := closedSubgroupTangentSubmodule (I := I) K hK
        let A : ℝ → GroupLieAlgebra I G := fun s =>
          tangentAd (I := I) (mulInvariantExp (I := I) (G := G) (s • X)) Y
        have hA (s : ℝ) : A s ∈ M := by
          let g : K := ⟨mulInvariantExp (I := I) (G := G) (s • X), hX s⟩
          have hg := tangentAd_mem_closedSubgroupTangentSubmodule
            (I := I) K hK hY g
          simpa only [M, A, g] using hg
        -- Expose the model-space representation required by the scalar derivative API.
        have hderiv : HasDerivAt (fun s : ℝ => show E from A s)
            (show E from LieAlgebra.ad ℝ (GroupLieAlgebra I G) X Y) 0 := by
          simpa only [A] using
            hasDerivAt_tangentAd_mulInvariantExp_smul_apply_zero (I := I) (G := G) X Y
        apply
          (closedSubgroupTangentSubmodule (I := I) K hK).closed_of_finiteDimensional.mem_of_tendsto
            hderiv.tendsto_slope_zero
        exact Eventually.of_forall fun s => by
          -- Expose the submodule carrier and the slope defining the derivative.
          change s⁻¹ • (A (0 + s) - A 0) ∈
            (closedSubgroupTangentSubmodule (I := I) K hK :
              Submodule ℝ (GroupLieAlgebra I G))
          simpa only [M, zero_add] using M.smul_mem s⁻¹ (M.sub_mem (hA s) (hA 0)) }

/-- The Lie subalgebra of a closed subgroup consists of the left-invariant derivations whose
complete exponential lines stay in the subgroup. -/
def lieSubalgebraOfClosedSubgroup (K : Subgroup G) (hK : IsClosed (K : Set G)) :
    LieSubalgebra ℝ (LeftInvariantDerivation I G) := by
  let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
  exact (closedSubgroupTangentLieSubalgebra (I := I) K hK).comap
    (leftInvariantDerivationLieEquivGroupLieAlgebra
      (I := I) (G := G) BoundarylessManifold.isInteriorPoint)

/-- Membership in the Lie subalgebra of a closed subgroup is characterized by containment of the
whole exponential line. -/
@[simp]
theorem mem_lieSubalgebraOfClosedSubgroup_iff
    (K : Subgroup G) (hK : IsClosed (K : Set G)) (X : LeftInvariantDerivation I G) :
    let _ : BoundarylessManifold I G := ContMDiffMul.boundarylessManifold
    let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
    X ∈ lieSubalgebraOfClosedSubgroup (I := I) K hK ↔
      ∀ t : ℝ, lieExp (I := I) (t • X) ∈ K := by
  let _ : BoundarylessManifold I G := ContMDiffMul.boundarylessManifold
  let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
  dsimp only
  -- Unfold the comap carrier before translating the tangent exponential to `lieExp`.
  change (∀ t : ℝ, mulInvariantExp (I := I) (G := G)
      (t • leftInvariantDerivationLieEquivGroupLieAlgebra
        (I := I) (G := G) BoundarylessManifold.isInteriorPoint X) ∈ K) ↔ _
  simp only [lieExp_eq_mulInvariantExp, map_smul,
    leftInvariantDerivationLieEquivGroupLieAlgebra_apply]

end TauCeti.Lie
