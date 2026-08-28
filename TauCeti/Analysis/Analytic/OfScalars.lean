module

public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.Analysis.Analytic.OfScalars

/-!
# Composition of scalar formal multilinear series

This file computes the formal composition of two scalar series in an arbitrary algebra.  The
algebra need not be commutative: variables retain their original order inside every composition
block.
-/

@[expose] public section

open scoped BigOperators

namespace FormalMultilinearSeries

variable {𝕜 E : Type*} [Field 𝕜] [Ring E] [Algebra 𝕜 E] [TopologicalSpace E]
  [IsTopologicalRing E]

/-- Coefficients of the formal composition of two scalar series.  As for
`FormalMultilinearSeries.comp`, the constant coefficient of the inner series is ignored. -/
def scalarComp (c d : ℕ → 𝕜) (n : ℕ) : 𝕜 :=
  ∑ p : Composition n, c p.length * ∏ i, d (p.blocksFun i)

private theorem List.prod_map_smul_map {ι : Type*} (l : List ι) (a : ι → 𝕜) (b : ι → E) :
    (l.map fun i ↦ a i • b i).prod = (l.map a).prod • (l.map b).prod := by
  induction l with
  | nil => simp
  | cons i l ih => simp only [List.map_cons, List.prod_cons, ih, smul_mul_smul_comm]

private theorem ofFn_embedding_eq_block {n : ℕ} (p : Composition n) (v : Fin n → E)
    (i : Fin p.length) :
    List.ofFn (fun j : Fin (p.blocksFun i) ↦ v (p.embedding i j)) =
      ((List.ofFn v).splitWrtComposition p).get
        ⟨i, by simpa using i.isLt⟩ := by
  apply List.ext_getElem
  · have h := congrArg (fun l ↦ l[i]) (List.map_length_splitWrtComposition (List.ofFn v) p)
    simpa [Composition.ofFn_blocksFun] using h.symm
  · intro j hj₁ hj₂
    rw [List.getElem_ofFn]
    rw [List.get_eq_getElem, List.getElem_splitWrtComposition]
    simp only [List.getElem_drop, List.getElem_take, List.getElem_ofFn,
      Composition.coe_embedding]

private theorem prod_blocks {n : ℕ} (p : Composition n) (v : Fin n → E) :
    (List.ofFn fun i : Fin p.length ↦
        (List.ofFn fun j : Fin (p.blocksFun i) ↦ v (p.embedding i j)).prod).prod =
      (List.ofFn v).prod := by
  have h :
      List.ofFn (fun i : Fin p.length ↦
          (List.ofFn fun j : Fin (p.blocksFun i) ↦ v (p.embedding i j)).prod) =
        ((List.ofFn v).splitWrtComposition p).map List.prod := by
    apply List.ext_getElem
    · simp
    · intro i hi₁ hi₂
      simp only [List.getElem_ofFn, List.getElem_map]
      exact congrArg List.prod (ofFn_embedding_eq_block p v ⟨i, by simpa using hi₁⟩)
  rw [h, ← List.prod_flatten, List.flatten_splitWrtComposition]

private theorem prod_applyComposition_ofScalars {n : ℕ} (d : ℕ → 𝕜) (p : Composition n)
    (v : Fin n → E) :
    (List.ofFn fun i : Fin p.length ↦
        (ofScalars E d).applyComposition p v i).prod =
      (∏ i, d (p.blocksFun i)) • (List.ofFn v).prod := by
  simp only [applyComposition, ofScalars, ContinuousMultilinearMap.smul_apply,
    ContinuousMultilinearMap.mkPiAlgebraFin_apply]
  rw [List.prod_map_smul_map]
  simp only [List.map_ofFn, Fin.prod_ofFn, prod_blocks]

/-- Composing two scalar formal multilinear series gives the scalar series whose coefficients are
obtained by summing over compositions.  This remains valid for noncommutative target algebras. -/
theorem ofScalars_comp_ofScalars (c d : ℕ → 𝕜) :
    (ofScalars E c).comp (ofScalars E d) = ofScalars E (scalarComp c d) := by
  ext n v
  simp only [FormalMultilinearSeries.comp, compAlongComposition_apply, ofScalars,
    ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.mkPiAlgebraFin_apply,
    scalarComp, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [prod_applyComposition_ofScalars]
  simp only [smul_smul]

end FormalMultilinearSeries
