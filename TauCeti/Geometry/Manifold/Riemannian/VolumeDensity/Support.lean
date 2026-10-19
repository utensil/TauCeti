/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Volume
public import Mathlib.MeasureTheory.Measure.Support

/-!
# Full support of Riemannian volume

The Riemannian volume measure of a continuous finite-dimensional Riemannian manifold is positive on
nonempty open sets. This gives the full-support interface used by later integration and positivity
arguments.
-/

public section

open Bundle MeasureTheory Set
open scoped Manifold Topology

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [MeasurableSpace M] [BorelSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- Riemannian volume is positive on every nonempty open set. -/
instance isOpenPosMeasure_riemannianVolume [LindelofSpace M] :
    Measure.IsOpenPosMeasure (riemannianVolume I M) where
  open_pos U hU hne := by
    obtain ⟨x, hx⟩ := hne
    let s := U ∩ (chartAt H x).source
    have hs : IsOpen s := hU.inter (chartAt H x).open_source
    have hne_s : s.Nonempty := ⟨x, hx, mem_chart_source H x⟩
    have hpos_chart : 0 < chartRiemannianVolume (I := I) x s :=
      chartRiemannianVolume_pos_of_isOpen_subset_source x hs inter_subset_right hne_s
    have hpos : 0 < riemannianVolume I M s := by
      rw [riemannianVolume_apply_of_subset inter_subset_right]
      exact hpos_chart
    exact (lt_of_lt_of_le hpos (measure_mono inter_subset_left)).ne'

/-- A continuous nonnegative function which is positive somewhere has strictly positive lower
Lebesgue integral against the Riemannian volume.  The statement uses the lower integral so it
remains meaningful without an integrability hypothesis. -/
theorem lintegral_riemannianVolume_pos [SigmaCompactSpace M]
    {f : M → ℝ} (hf : Continuous f) (hnn : ∀ x, 0 ≤ f x) (hpos : ∃ x, 0 < f x) :
    0 < ∫⁻ x, ENNReal.ofReal (f x) ∂riemannianVolume I M := by
  have hmeas : Measurable (fun x ↦ ENNReal.ofReal (f x)) :=
    hf.measurable.ennreal_ofReal
  rw [lintegral_pos_iff_support hmeas]
  obtain ⟨x, hx⟩ := hpos
  have hset : {y | f y ≠ 0} = {y | 0 < f y} := by
    ext y
    constructor
    · intro hy
      exact lt_of_le_of_ne (hnn y) (Ne.symm hy)
    · intro hy
      exact ne_of_gt (show 0 < f y from hy)
  have hopen : IsOpen {y | f y ≠ 0} := by
    rw [hset]
    exact hf.isOpen_preimage _ isOpen_Ioi
  have hmeasure : 0 < riemannianVolume I M {y | f y ≠ 0} :=
    IsOpen.measure_pos _ hopen ⟨x, ne_of_gt hx⟩
  apply lt_of_lt_of_le hmeasure
  apply measure_mono
  intro y hy
  have hy' : y ∈ {z | 0 < f z} := hset ▸ hy
  exact (ENNReal.ofReal_pos.mpr hy').ne'

end TauCeti

end
