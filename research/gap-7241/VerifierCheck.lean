module
import all RiemannMasullo.Ch10_TraceSpectral.Sec3
import all RiemannMasullo.Ch10_TraceSpectral.Sec2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.LocallyConvex.Barrelled
import RiemannMasullo.ForMathlib.Analysis.Distribution.SchwartzSpace.Complete

/-!
Scratch file for the referee pass on the two residue lemmas of Ch10 Sec3
(`spectralLineConvolution_traceCauchy_scalar_shell`, issue 7240, and
`spectralStripConvolution_traceCauchy_compact_block_series`, issue 7241).
Nothing here is part of the library. Each main theorem takes the conclusion of one
residue lemma as a hypothesis and derives a statement about the zeros of one row.

Check with `lake lean .agent/TraceCauchyReferee.lean` (about one minute).

* Parts A, B: abstract steps; a norm twist is an eigenfunctional of every transposed convolution.
* Part C (strip, one test): `referee_strip_block_bound`, `referee_strip_two_zero`.
* Parts D, E (line, one test): `referee_line_block_bound_all`, `referee_line_mellin_gap`.
* Part F (strip of width zero, one test): `referee_strip_zero_width_mellin_gap`.
* Part G (strip of width zero, all tests): `referee_strip_zero_width_uniform`,
  `referee_strip_zero_width_gap`, `referee_strip_zero_width_gap_of_statement`.
* Parts H, I (line, all tests): `referee_line_uniform`, `referee_line_gap`,
  `referee_line_zero_isolated`, `referee_line_gap_all`, `referee_line_gap_of_statement`.

The two final theorems, `referee_strip_zero_width_gap_of_statement` and
`referee_line_gap_of_statement`, say: if the proposition asserted by the residue lemma holds
for one centre `a`, one choice of lifts and one Sobolev exponent above 3, then in every row
there are `C` and `N` with `1 ≤ C (1 + |t|)^N |t − t'|` for all distinct zeros `a + i t`,
`a + i t'` of the completed L-function of that row which have a surviving zeroth jet.
The theorems whose names end in `_library` or `_check` plug in the library lemmas themselves
and therefore show `sorryAx`; all the others use only the three standard axioms.
-/

noncomputable section

open Filter Function MeasureTheory NumberField Set
open scoped BigOperators NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

/-! ## Part A: abstract steps -/

theorem referee_norm_smul {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (c : ℂ) (Λ : StrongDual ℂ H) : ‖c • Λ‖ = ‖c‖ * ‖Λ‖ := norm_smul c Λ

/-- If `Re f w ≤ δ` whenever `‖Φ‖ ‖w‖ ≤ 1`, then `‖f‖ ≤ δ ‖Φ‖`. -/
theorem referee_opNorm_le_of_unit_tests {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (f Φ : StrongDual ℂ H) (δ : ℝ)
    (h : ∀ w : H, ‖Φ‖ * ‖w‖ ≤ 1 → (f w).re ≤ δ) : ‖f‖ ≤ δ * ‖Φ‖ := by
  have h' (w : H) (hw : ‖Φ‖ * ‖w‖ ≤ 1) : ‖f w‖ ≤ δ := by
    obtain ⟨c, hc1, hc⟩ := Complex.exists_norm_eq_mul_self (f w)
    have hcw : ‖Φ‖ * ‖c • w‖ ≤ 1 := by rwa [norm_smul, hc1, one_mul]
    have := h (c • w) hcw
    rwa [map_smul, smul_eq_mul, ← hc, Complex.ofReal_re] at this
  have hδ : 0 ≤ δ := by
    have := h' 0 (by simp)
    simpa using this
  refine ContinuousLinearMap.opNorm_le_bound f (mul_nonneg hδ (norm_nonneg Φ)) fun w ↦ ?_
  by_cases hpos : 0 < ‖Φ‖ * ‖w‖
  · have hr : ‖Φ‖ * ‖(((‖Φ‖ * ‖w‖)⁻¹ : ℝ) : ℂ) • w‖ ≤ 1 := by
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hpos.le)]
      have : ‖Φ‖ * ((‖Φ‖ * ‖w‖)⁻¹ * ‖w‖) = (‖Φ‖ * ‖w‖)⁻¹ * (‖Φ‖ * ‖w‖) := by ring
      rw [this, inv_mul_cancel₀ hpos.ne']
    have h1 := h' _ hr
    rw [map_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hpos.le),
      inv_mul_le_iff₀ hpos] at h1
    linarith
  · have hzero : ‖Φ‖ * ‖w‖ = 0 :=
      le_antisymm (not_lt.mp hpos) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    have hfw : ‖f w‖ ≤ 0 := by
      by_contra hne
      push_neg at hne
      obtain ⟨n, hn⟩ := exists_nat_gt (δ / ‖f w‖)
      have hsm : ‖Φ‖ * ‖((n : ℝ) : ℂ) • w‖ ≤ 1 := by
        rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (Nat.cast_nonneg n)]
        have : ‖Φ‖ * ((n : ℝ) * ‖w‖) = (n : ℝ) * (‖Φ‖ * ‖w‖) := by ring
        rw [this, hzero, mul_zero]
        exact zero_le_one
      have h1 := h' _ hsm
      rw [map_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg (Nat.cast_nonneg n)] at h1
      rw [div_lt_iff₀ hne] at hn
      linarith
    have : δ * ‖Φ‖ * ‖w‖ = 0 := by rw [mul_assoc, hzero, mul_zero]
    rw [this]
    exact hfw

/-- A scalar estimate for one block, tested on all finite families whose synthesis
operator is a contraction, bounds the transposed image of each jet of the block by the
distance from that jet to the span of the jets outside the block. No biorthogonal
vectors are needed. -/
theorem referee_block_conditioning {H J : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [DecidableEq J] (A : H →L[ℂ] H) (Λ : J → StrongDual ℂ H) (n : ℕ) (jet : Fin n → J)
    (hjet : Injective jet) (δ : ℝ)
    (hblock : ∀ (K : Finset J) (v : J → H), (∀ k ∉ K, v k = 0) →
      ‖∑ k ∈ K, (Λ k).smulRight (v k)‖ ≤ 1 →
      (∑ m : Fin n, Λ (jet m) (A (v (jet m)))).re ≤ δ)
    (m₀ : Fin n) (K' : Finset J) (c : J → ℂ) (hK' : ∀ k ∈ K', ∀ m, k ≠ jet m) :
    ‖(Λ (jet m₀)).comp A‖ ≤ δ * ‖Λ (jet m₀) - ∑ k ∈ K', c k • Λ k‖ := by
  apply referee_opNorm_le_of_unit_tests
  intro w hw
  let v : J → H := fun k ↦ if k = jet m₀ then w else if k ∈ K' then -(c k • w) else 0
  have hnot : jet m₀ ∉ K' := fun hmem ↦ hK' _ hmem m₀ rfl
  have hvm : v (jet m₀) = w := if_pos rfl
  have hvK (k : J) (hk : k ∈ K') : v k = -(c k • w) := by
    have hne : k ≠ jet m₀ := hK' k hk m₀
    change (if k = jet m₀ then w else if k ∈ K' then -(c k • w) else 0) = _
    rw [if_neg hne, if_pos hk]
  have hv0 : ∀ k ∉ insert (jet m₀) K', v k = 0 := by
    intro k hk
    rw [Finset.mem_insert, not_or] at hk
    change (if k = jet m₀ then w else if k ∈ K' then -(c k • w) else 0) = _
    rw [if_neg hk.1, if_neg hk.2]
  have hsum : ∑ k ∈ insert (jet m₀) K', (Λ k).smulRight (v k) =
      (Λ (jet m₀) - ∑ k ∈ K', c k • Λ k).smulRight w := by
    rw [Finset.sum_insert hnot]
    ext y
    have hrest : ∀ k ∈ K', (Λ k) y • v k = -((c k * Λ k y) • w) := by
      intro k hk
      rw [hvK k hk, smul_neg, smul_smul, mul_comm]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [Finset.sum_congr rfl hrest, hvm, Finset.sum_neg_distrib, ← Finset.sum_smul, sub_smul]
    abel
  have hnorm : ‖∑ k ∈ insert (jet m₀) K', (Λ k).smulRight (v k)‖ ≤ 1 := by
    rw [hsum, ContinuousLinearMap.norm_smulRight_apply]
    exact hw
  have hmain := hblock (insert (jet m₀) K') v hv0 hnorm
  have hsingle : ∑ m : Fin n, Λ (jet m) (A (v (jet m))) = Λ (jet m₀) (A w) := by
    rw [Finset.sum_eq_single m₀]
    · rw [hvm]
    · intro m _ hm
      have hne : jet m ≠ jet m₀ := fun h ↦ hm (hjet h)
      have hout : jet m ∉ K' := fun hmem ↦ hK' _ hmem m rfl
      have hz : v (jet m) = 0 := by
        change (if jet m = jet m₀ then w else if jet m ∈ K' then -(c (jet m) • w) else 0) = _
        rw [if_neg hne, if_neg hout]
      rw [hz, map_zero, map_zero]
    · intro h
      exact absurd (Finset.mem_univ m₀) h
  rw [hsingle] at hmain
  exact hmain

/-- Anchored shell estimates for a numbering whose second coordinate is injective give
the same estimate, with twice the constant, for every single block beyond the anchor column:
the block is the difference of two shells over the same anchor. -/
theorem referee_shell_block {H J Z : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [DecidableEq Z] (A : H →L[ℂ] H) (Λ : J → StrongDual ℂ H) (N : Z → ℕ)
    (jet : (z : Z) → Fin (N z) → J) (e : Z ↪ ℕ × ℕ) (he : Injective fun z ↦ (e z).2)
    (ε : ℝ) (i : ℕ × ℕ)
    (hsh : ∀ j ≥ i, ∀ (K : Finset J) (v : J → H), (∀ k ∉ K, v k = 0) →
      ‖∑ k ∈ K, (Λ k).smulRight (v k)‖ ≤ 1 →
      (∑ z ∈ ((Finset.Iic j.1).product (Finset.Iic j.2)).preimage e e.injective.injOn \
          ((Finset.Iic i.1).product (Finset.Iic i.2)).preimage e e.injective.injOn,
        ∑ m : Fin (N z), Λ (jet z m) (A (v (jet z m)))).re ≤ ε)
    (z : Z) (hz : i.2 < (e z).2) (K : Finset J) (v : J → H) (hv : ∀ k ∉ K, v k = 0)
    (hn : ‖∑ k ∈ K, (Λ k).smulRight (v k)‖ ≤ 1) :
    (∑ m : Fin (N z), Λ (jet z m) (A (v (jet z m)))).re ≤ 2 * ε := by
  let box (ij : ℕ × ℕ) : Finset Z :=
    ((Finset.Iic ij.1).product (Finset.Iic ij.2)).preimage e e.injective.injOn
  have hmem (u : Z) (ij : ℕ × ℕ) : u ∈ box ij ↔ (e u).1 ≤ ij.1 ∧ (e u).2 ≤ ij.2 := by
    simp only [box, Finset.mem_preimage]
    constructor
    · intro h
      obtain ⟨h₁, h₂⟩ := Finset.mem_product.mp h
      exact ⟨Finset.mem_Iic.mp h₁, Finset.mem_Iic.mp h₂⟩
    · intro h
      exact Finset.mem_product.mpr ⟨Finset.mem_Iic.mpr h.1, Finset.mem_Iic.mpr h.2⟩
  let row := max i.1 (e z).1
  let col := (e z).2
  have hj : (row, col) ≥ i := ⟨le_max_left _ _, hz.le⟩
  have hj' : (row, col - 1) ≥ i := ⟨le_max_left _ _, by change i.2 ≤ col - 1; omega⟩
  have zin : z ∈ box (row, col) := (hmem _ _).2 ⟨le_max_right _ _, le_rfl⟩
  have znot' : z ∉ box (row, col - 1) := by
    intro h
    have := ((hmem _ _).1 h).2
    change col ≤ col - 1 at this
    omega
  have znoti : z ∉ box i := by
    intro h
    have := ((hmem _ _).1 h).2
    omega
  have hbox : box (row, col) = insert z (box (row, col - 1)) := by
    ext u
    by_cases hu : u = z
    · subst hu
      simp only [zin, Finset.mem_insert, true_or]
    · have hcol : (e u).2 ≠ col := fun h ↦ hu (he h)
      rw [Finset.mem_insert, or_iff_right hu, hmem, hmem]
      change _ ∧ (e u).2 ≤ col ↔ _ ∧ (e u).2 ≤ col - 1
      omega
  have hshell : box (row, col) \ box i = insert z (box (row, col - 1) \ box i) := by
    rw [hbox, Finset.insert_sdiff_of_notMem _ znoti]
  have znotshell : z ∉ box (row, col - 1) \ box i := fun h ↦ znot' (Finset.mem_sdiff.mp h).1
  have h1 := hsh (row, col) hj K v hv hn
  change (∑ u ∈ box (row, col) \ box i, ∑ m : Fin (N u), Λ (jet u m) (A (v (jet u m)))).re ≤ ε
    at h1
  rw [hshell, Finset.sum_insert znotshell, Complex.add_re] at h1
  have hvneg : ∀ k ∉ K, (fun k ↦ -v k) k = 0 := fun k hk ↦ by simp only [hv k hk, neg_zero]
  have hnneg : ‖∑ k ∈ K, (Λ k).smulRight ((fun k ↦ -v k) k)‖ ≤ 1 := by
    have : ∑ k ∈ K, (Λ k).smulRight ((fun k ↦ -v k) k) = -∑ k ∈ K, (Λ k).smulRight (v k) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      ext y
      simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.neg_apply, smul_neg]
    rw [this, norm_neg]
    exact hn
  have h2 := hsh (row, col - 1) hj' K (fun k ↦ -v k) hvneg hnneg
  change (∑ u ∈ box (row, col - 1) \ box i,
    ∑ m : Fin (N u), Λ (jet u m) (A (-v (jet u m)))).re ≤ ε at h2
  simp only [map_neg, Finset.sum_neg_distrib, Complex.neg_re] at h2
  linarith

/-- One block of a biorthogonal system: a functional which differs from the `m`-th jet by
something vanishing on the vectors of the block recovers the transposed jet from the
finite section of that block. -/
theorem referee_single_block {H J Z : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (A : H →L[ℂ] H) (x : J → H) (Λ : J → StrongDual ℂ H)
    (hb : IsSpectralMarkushevichBasis x Λ) (N : Z → ℕ) (jet : (z : Z) → Fin (N z) → J)
    (z : Z) (hjet : Injective (jet z)) (m : Fin (N z)) (Ψ : StrongDual ℂ H)
    (hΨ : ∀ n, Ψ (x (jet z n)) = 0) :
    (Λ (jet z m) - Ψ).comp (spectralConvolutionFiniteSum A x Λ {z} N jet) =
      (Λ (jet z m)).comp A := by
  ext v
  have hB : spectralConvolutionFiniteSum A x Λ {z} N jet v =
      ∑ n : Fin (N z), Λ (jet z n) (A v) • x (jet z n) := by
    simp only [spectralConvolutionFiniteSum, Finset.sum_singleton, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply]
  rw [ContinuousLinearMap.comp_apply, hB, ContinuousLinearMap.comp_apply, map_sum]
  rw [Finset.sum_eq_single m]
  · rw [map_smul, ContinuousLinearMap.sub_apply, hb.1, hΨ, sub_zero, smul_eq_mul, mul_one]
  · intro n _ hn
    rw [map_smul, ContinuousLinearMap.sub_apply, hb.2.1 _ _ (fun h ↦ hn (hjet h)), hΨ, sub_zero,
      smul_zero]
  · intro h
    exact absurd (Finset.mem_univ m) h

#print axioms referee_block_conditioning
#print axioms referee_shell_block
#print axioms referee_single_block

/-! ## Part B: the concrete setting -/

variable {F : Type*} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" =>
  (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "W(" l ", " r ", " s ")" =>
  CompactIntervalSobolev μ𝔽 (fun g : C𝔽 ↦ Real.log ((ideleClassNorm F g).val : ℝ)) l r s
local notation "Θ(" a ", " hI ", " hs ")" => globalThetaSobolev F a hI hs
local notation "Q(" a ", " hI ", " hs ")" => spectralSobolevQuotient F a hI hs
local notation "h₀" => le_rfl (a := (0 : ℝ))
local notation "hStrip(" hα ")" => (neg_nonpos.mpr hα |>.trans hα)
local notation "hs₀(" hs ")" => le_of_lt (zero_lt_one.trans hs)
local notation "shift(" b ", " t ")" => ((b : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I
local notation "order(" χ ", " z ")" => meromorphicOrderAt (continuedCompletedHeckeL (F := F) χ) z
local notation "mult(" χ ", " z ")" => (order(χ, z)).untop₀.toNat
local notation "hm𝔽" => (⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ :
  IsModulation m𝔽)
local notation "M(" φ ", " χ ", " z ")" =>
  modulatedFourierMellin m𝔽 univ hm𝔽 μ𝔽
    (φ : BruhatCompactSupport C𝔽).val (ideleClassNormTwist (F := F) χ z)

/-- A functional on the quotient whose reciprocal-weight realization is the class of `c`
evaluates on a representative by the unweighted product integral. Same argument as
`spectralStripConvolution_jet_eval`, for an arbitrary base interval. -/
theorem referee_dual_eval (a : ℝ) {l r s : ℝ} (hI : l ≤ r) (hs : 0 ≤ s)
    (f : StrongDual ℂ Q(a, hI, hs)) (c : C𝔽 → ℂ)
    (hc : MemLp c 2 (μ𝔽 |>.withDensity fun g ↦
      ENNReal.ofReal (intervalSobolevDensity l r s (logIdeleClassNorm F g))⁻¹))
    (hf : spectralSobolevDualEmbedding F a hI hs f = hc.toLp c) (v : W(l, r, s)) :
    Integrable (fun y ↦ v y * c y) μ𝔽 ∧
      f ((Θ(a, hI, hs)).mkQL v) = ∫ y, v y * c y ∂μ𝔽 := by
  let w (g : C𝔽) := intervalSobolevDensity l r s (logIdeleClassNorm F g)
  have hw : Measurable w := by
    have hD : Continuous (intervalSobolevDensity l r s) := by
      unfold intervalSobolevDensity
      fun_prop
    exact hD.measurable.comp ((NNReal.continuous_coe.comp
      (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous)).measurable.log)
  have habs : μ𝔽 ≪ (μ𝔽).withDensity (fun g ↦ ENNReal.ofReal (w g)⁻¹) := by
    refine withDensity_absolutelyContinuous' hw.inv.ennreal_ofReal.aemeasurable (.of_forall fun g ↦ ?_)
    refine ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr ?_)
    exact mul_pos (lt_max_of_lt_left (Real.exp_pos _)) (Real.rpow_pos_of_pos (by positivity) _)
  have hae : (spectralSobolevDualEmbedding F a hI hs f : C𝔽 → ℂ) =ᵐ[μ𝔽] c := by
    rw [hf]
    exact habs.ae_le (MemLp.coeFn_toLp _)
  have he := spectralSobolevPairing_dual hI hs (f.comp ((Θ(a, hI, hs)).mkQL)) v
  change Integrable (fun y ↦ v y * spectralSobolevDualEmbedding F a hI hs f y) μ𝔽 ∧
      f ((Θ(a, hI, hs)).mkQL v) = ∫ y, v y * spectralSobolevDualEmbedding F a hI hs f y ∂μ𝔽 at he
  have hEq := hae.mono fun y hy ↦ congrArg (v y * ·) hy
  exact ⟨he.1.congr hEq, he.2.trans (integral_congr_ae hEq)⟩

/-- A functional on the quotient realized by a norm twist of a unitary character is an
eigenfunctional of the transpose of every convolution, with the Mellin value as eigenvalue.
Same argument as `spectralStripConvolution_jet_top` at jet order zero, for an arbitrary
base interval. -/
theorem referee_twist_eigen (a : ℝ) {l r s : ℝ} (hI : l ≤ r) (hs : 0 ≤ s)
    (f : StrongDual ℂ Q(a, hI, hs)) (η : PontryaginDual C𝔽) (z : ℂ) (c : C𝔽 → ℂ)
    (hc : MemLp c 2 (μ𝔽 |>.withDensity fun g ↦
      ENNReal.ofReal (intervalSobolevDensity l r s (logIdeleClassNorm F g))⁻¹))
    (hf : spectralSobolevDualEmbedding F a hI hs f = hc.toLp c)
    (hcT : ∀ g, c g = ideleClassNormTwist (F := F) η z g)
    (φ : BruhatCompactSupport C𝔽) (u : Q(a, hI, hs)) :
    f (spectralConvolution (F := F) a hI hs φ u) = M(φ, η, z) * f u := by
  let θ := globalThetaSobolev F a hI hs
  obtain ⟨v, hv⟩ := θ.mkQ_surjective u
  let T := ideleClassNormTwist (F := F) η z
  let τ := hardySobolevTranslation μ𝔽 m𝔽 l r s hI hs
  let ℓ := f.comp θ.mkQL
  have heval (w : W(l, r, s)) : f (θ.mkQL w) = ∫ y, w y * T y ∂μ𝔽 :=
    (referee_dual_eval (F := F) a hI hs f c hc hf w).2.trans
      (integral_congr_ae (.of_forall fun y ↦ congrArg (w y * ·) (hcT y)))
  have htop : ∫ y, v y * T y ∂μ𝔽 = f u := (heval v).symm.trans (congrArg f hv)
  have htr (g : C𝔽) : ∫ y, τ g v y * T y ∂μ𝔽 = T g * ∫ y, v y * T y ∂μ𝔽 := by
    let Hf (y : C𝔽) := v (g⁻¹ * y) * T y
    calc
      _ = ∫ y, Hf y ∂μ𝔽 := integral_congr_ae
        ((hardySobolevTranslation_apply μ𝔽 m𝔽 l r s hI hs g v).mono
          fun y hy ↦ congrArg (· * T y) hy)
      _ = ∫ y, Hf (g * y) ∂μ𝔽 := (integral_mul_left_eq_self Hf g).symm
      _ = ∫ y, T g * (v y * T y) ∂μ𝔽 := by
        refine integral_congr_ae (.of_forall fun y ↦ ?_)
        change v (g⁻¹ * (g * y)) * T (g * y) = T g * (v y * T y)
        rw [inv_mul_cancel_left, map_mul]
        ring
      _ = _ := integral_const_mul _ _
  have hτ (g : C𝔽) : ℓ (τ g v) = T g * f u :=
    (heval (τ g v)).trans ((htr g).trans (congrArg (T g * ·) htop))
  have hP := bruhatRegularizedAction_apply μ𝔽 τ
    (exists_hardySobolevTranslation μ𝔽 m𝔽 l r s hI hs).choose_spec.2 φ v
  have he := congrArg (fun p : PettisWeakCompletion W(l, r, s) ↦
    (show Module.Dual ℂ (StrongDual ℂ W(l, r, s)) from p) ℓ) hP.2
  change ℓ (hardySobolevTestAction μ𝔽 m𝔽 l r s hI hs φ v) =
    ∫ g, ℓ (φ.val g • τ g v) ∂μ𝔽 at he
  have hM := (spectralConvolution_mellin_integrable φ η z).2
  calc
    _ = ℓ (hardySobolevTestAction μ𝔽 m𝔽 l r s hI hs φ v) :=
      (congrArg (fun w ↦ f (spectralConvolution (F := F) a hI hs φ w)) hv.symm).trans
        (congrArg f (spectralConvolution_mkQ a hI hs φ v))
    _ = ∫ g, ℓ (φ.val g • τ g v) ∂μ𝔽 := he
    _ = ∫ g, (φ.val g * T g) * f u ∂μ𝔽 := integral_congr_ae (.of_forall fun g ↦ by
      exact (map_smul ℓ _ _).trans ((congrArg (φ.val g * ·) (hτ g)).trans (mul_assoc _ _ _).symm))
    _ = _ := (integral_mul_const _ _).trans (congrArg (· * f u) hM.symm)

#print axioms referee_twist_eigen

/-! ## Part C: the strip residue lemma (issue 7241) -/

section Strip

variable (a : ℝ)

local notation "Zs(" χ ", " α ")" => {z : PontryaginDual C₁ × ℝ × ℝ //
  z.2.1 ∈ Icc (-α) α ∧ 0 < order(χ z.1, shift(a + z.2.1, z.2.2))}
local notation "Ns(" χ ", " α ", " s ", " z ")" => spectralStripMultiplicity α s (z).val.2.1
  (mult(χ (z).val.1, shift(a + (z).val.2.1, (z).val.2.2)))

/-- The conclusion `h` of `spectralStripConvolution_traceCauchy_compact_block_series`, for one
test, forces one constant `c` with
`|M_φ(z)| ‖Λ_{z,0}‖ ≤ c ‖Λ_{z,0} − Ψ‖`
for every zero `z` of the strip with a surviving zeroth jet and every functional `Ψ` which
vanishes on the biorthogonal vectors of the block of `z`. -/
theorem referee_strip_block_bound (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    {α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s) (φ : BruhatCompactSupport C𝔽)
    (x : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s → Q(a, hStrip(hα), hs₀(hs)))
    (Λ : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s → StrongDual ℂ Q(a, hStrip(hα), hs₀(hs)))
    (hb : IsSpectralMarkushevichBasis x Λ)
    (hj : ∀ j, spectralSobolevDualEmbedding F a hStrip(hα) hs₀(hs) (Λ j) =
      (spectralStripJet_memLp (F := F) (fun ω ↦ χ ω) hα hs₀(hs) j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2))
    (h : let H := Q(a, hStrip(hα), hs₀(hs))
      let A := spectralConvolution (F := F) a hStrip(hα) hs₀(hs) φ
      let jet (z : Zs(χ, α)) (m : Fin (Ns(χ, α, s, z))) :
          SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s :=
        ⟨(z.val.1, z.val.2.1, z.val.2.2, m.val), m.isLt⟩
      ∀ U : compactOperator (RingHom.id ℂ) H H,
        Summable (fun z : Zs(χ, α) ↦ ∑ m, Λ (jet z m) (A (U.val (x (jet z m)))))) :
    ∃ c : ℝ, ∀ (z : Zs(χ, α)) (hz : 0 < Ns(χ, α, s, z))
      (Ψ : StrongDual ℂ Q(a, hStrip(hα), hs₀(hs))),
      (∀ n : Fin (Ns(χ, α, s, z)),
        Ψ (x ⟨(z.val.1, z.val.2.1, z.val.2.2, n.val), n.isLt⟩) = 0) →
      ‖M(φ, χ z.val.1, shift(z.val.2.1, z.val.2.2))‖ *
          ‖Λ ⟨(z.val.1, z.val.2.1, z.val.2.2, 0), hz⟩‖ ≤
        c * ‖Λ ⟨(z.val.1, z.val.2.1, z.val.2.2, 0), hz⟩ - Ψ‖ := by
  classical
  let count (z : Zs(χ, α)) := Ns(χ, α, s, z)
  let jet (z : Zs(χ, α)) (m : Fin (count z)) :
      SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s :=
    ⟨(z.val.1, z.val.2.1, z.val.2.2, m.val), m.isLt⟩
  let A := spectralConvolution (F := F) a hStrip(hα) hs₀(hs) φ
  obtain ⟨R, hR, c, hc⟩ := spectralStripConvolution_traceCauchy_scalar_bound A x Λ count jet h
  refine ⟨c, fun z hz Ψ hΨ ↦ ?_⟩
  have hjet : Injective (jet z) := fun m n hmn ↦ Fin.ext
    (congrArg (fun q : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s ↦ q.val.2.2.2) hmn)
  let T := ∑ u ∈ ({z} : Finset Zs(χ, α)), R u
  have hT : T.val = spectralConvolutionFiniteSum A x Λ {z} count jet := hR {z}
  have htr : traceNorm T ≤ c := hc ⟨{z}, rfl⟩
  have hop : ‖T.val‖ ≤ traceNorm T := by
    rw [← approximationNumber_zero_eq_opNorm T.val
      (isCompactOperator_of_isNuclearOperator T.property)]
    simpa using spectralConvolutionFiniteSum_limit_of_traceCauchy_bound T {0}
  have hcomp := referee_single_block A x Λ hb count jet z hjet ⟨0, hz⟩ Ψ hΨ
  have heig : (Λ (jet z ⟨0, hz⟩)).comp A =
      M(φ, χ z.val.1, shift(z.val.2.1, z.val.2.2)) • Λ (jet z ⟨0, hz⟩) := by
    ext v
    exact spectralStripConvolution_jet_top a hα hs χ Λ hj φ z ⟨0, hz⟩ v
      (fun k hk ↦ absurd hk (Nat.not_lt_zero _))
  have hmain : ‖(Λ (jet z ⟨0, hz⟩)).comp A‖ ≤ ‖Λ (jet z ⟨0, hz⟩) - Ψ‖ * c := by
    rw [← hcomp, ← hT]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_left (hop.trans htr) (norm_nonneg _))
  rw [heig, referee_norm_smul] at hmain
  rw [mul_comm c]
  exact hmain

#print axioms referee_strip_block_bound

/-- The hypothesis `h` of `referee_strip_block_bound` is literally the conclusion of the
library's residue lemma: this term typechecks. It inherits the `sorry` of that lemma. -/
theorem referee_strip_from_library (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω))
    {α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s) (φ : BruhatCompactSupport C𝔽)
    (x : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s → Q(a, hStrip(hα), hs₀(hs)))
    (Λ : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s → StrongDual ℂ Q(a, hStrip(hα), hs₀(hs)))
    (_hb : IsSpectralMarkushevichBasis x Λ)
    (_hj : ∀ j, spectralSobolevDualEmbedding F a hStrip(hα) hs₀(hs) (Λ j) =
      (spectralStripJet_memLp (F := F) (fun ω ↦ χ ω) hα hs₀(hs) j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2)) :
    ∃ c : ℝ, ∀ (z : Zs(χ, α)) (hz : 0 < Ns(χ, α, s, z))
      (Ψ : StrongDual ℂ Q(a, hStrip(hα), hs₀(hs))),
      (∀ n : Fin (Ns(χ, α, s, z)),
        Ψ (x ⟨(z.val.1, z.val.2.1, z.val.2.2, n.val), n.isLt⟩) = 0) →
      ‖M(φ, χ z.val.1, shift(z.val.2.1, z.val.2.2))‖ *
          ‖Λ ⟨(z.val.1, z.val.2.1, z.val.2.2, 0), hz⟩‖ ≤
        c * ‖Λ ⟨(z.val.1, z.val.2.1, z.val.2.2, 0), hz⟩ - Ψ‖ :=
  referee_strip_block_bound a χ hα hs φ x Λ _hb _hj
    (spectralStripConvolution_traceCauchy_compact_block_series a χ _hχ hα hs φ x Λ _hb _hj)

#print axioms referee_strip_from_library

/-- Special case of `referee_strip_block_bound`: `Ψ` may be any jet at any other zero, since
it vanishes on the block of `z` by biorthogonality. -/
theorem referee_strip_two_zero (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    {α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s) (φ : BruhatCompactSupport C𝔽)
    (x : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s → Q(a, hStrip(hα), hs₀(hs)))
    (Λ : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s → StrongDual ℂ Q(a, hStrip(hα), hs₀(hs)))
    (hb : IsSpectralMarkushevichBasis x Λ)
    (hj : ∀ j, spectralSobolevDualEmbedding F a hStrip(hα) hs₀(hs) (Λ j) =
      (spectralStripJet_memLp (F := F) (fun ω ↦ χ ω) hα hs₀(hs) j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2))
    (h : let H := Q(a, hStrip(hα), hs₀(hs))
      let A := spectralConvolution (F := F) a hStrip(hα) hs₀(hs) φ
      let jet (z : Zs(χ, α)) (m : Fin (Ns(χ, α, s, z))) :
          SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s :=
        ⟨(z.val.1, z.val.2.1, z.val.2.2, m.val), m.isLt⟩
      ∀ U : compactOperator (RingHom.id ℂ) H H,
        Summable (fun z : Zs(χ, α) ↦ ∑ m, Λ (jet z m) (A (U.val (x (jet z m)))))) :
    ∃ c : ℝ, ∀ (z : Zs(χ, α)) (hz : 0 < Ns(χ, α, s, z))
      (k : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s),
      (k.val.1, k.val.2.1, k.val.2.2.1) ≠ z.val →
      ‖M(φ, χ z.val.1, shift(z.val.2.1, z.val.2.2))‖ *
          ‖Λ ⟨(z.val.1, z.val.2.1, z.val.2.2, 0), hz⟩‖ ≤
        c * ‖Λ ⟨(z.val.1, z.val.2.1, z.val.2.2, 0), hz⟩ - Λ k‖ := by
  obtain ⟨c, hc⟩ := referee_strip_block_bound a χ hα hs φ x Λ hb hj h
  refine ⟨c, fun z hz k hk ↦ hc z hz (Λ k) (fun n ↦ hb.2.1 _ _ ?_)⟩
  intro hEq
  apply hk
  subst hEq
  rfl

#print axioms referee_strip_two_zero

end Strip

/-! ## Part D: the line residue lemma (issue 7240) -/

section Line

variable (a : ℝ)

local notation "Zl(" χ ")" => {z : PontryaginDual C₁ × ℝ // 0 < order(χ z.1, shift(a, z.2))}
local notation "Nl(" χ ", " s ", " z ")" => spectralBoundaryMultiplicity s (mult(χ (z).val.1,
  shift(a, (z).val.2)))

open Classical in
/-- The conclusion `h` of `spectralLineConvolution_traceCauchy_scalar_shell`, for one test and
one numbering `e` of the zeros with pairwise distinct columns, forces: for every `ε > 0` and
all zeros `z` outside a finite set with a surviving zeroth jet,
`|M_φ(z)| ‖Λ_{z,0}‖ ≤ 2 ε ‖Λ_{z,0} − Ψ‖`
for every finite combination `Ψ` of jets at other zeros. No biorthogonal vectors enter. -/
theorem referee_line_block_bound (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    {s : ℝ} (hs : 1 < s) (φ : BruhatCompactSupport C𝔽)
    (e : Zl(χ) ↪ ℕ × ℕ) (hcol : Injective fun z ↦ (e z).2)
    (Λ : SpectralLineJetIndex (F := F) χ a s → StrongDual ℂ Q(a, h₀, hs₀(hs)))
    (hj : ∀ j, spectralSobolevDualEmbedding F a h₀ hs₀(hs) (Λ j) =
      (spectralLineJet_memLp (F := F) χ hs j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) 0 j.val.2.1 j.val.2.2))
    (h : let box (ij : ℕ × ℕ) :=
        ((Finset.Iic ij.1).product (Finset.Iic ij.2)).preimage e e.injective.injOn
      let jet (z : Zl(χ)) (m : Fin (Nl(χ, s, z))) : SpectralLineJetIndex (F := F) χ a s :=
        ⟨(z.val.1, z.val.2, m.val), m.isLt⟩
      let A := spectralConvolution (F := F) a h₀ hs₀(hs) φ
      ∀ ε > (0 : ℝ), ∃ i, ∀ j ≥ i, ∀ (K : Finset (SpectralLineJetIndex (F := F) χ a s))
        (v : SpectralLineJetIndex (F := F) χ a s → Q(a, h₀, hs₀(hs))),
        (∀ k ∉ K, v k = 0) → ‖∑ k ∈ K, (Λ k).smulRight (v k)‖ ≤ 1 →
        (∑ z ∈ box j \ box i, ∑ m : Fin (Nl(χ, s, z)), Λ (jet z m) (A (v (jet z m)))).re ≤ ε) :
    ∀ ε > (0 : ℝ), ∃ S : Finset Zl(χ), ∀ z ∉ S, ∀ (hz : 0 < Nl(χ, s, z))
      (K' : Finset (SpectralLineJetIndex (F := F) χ a s))
      (c : SpectralLineJetIndex (F := F) χ a s → ℂ),
      (∀ k ∈ K', (k.val.1, k.val.2.1) ≠ z.val) →
      ‖M(φ, χ z.val.1, shift(0, z.val.2))‖ * ‖Λ ⟨(z.val.1, z.val.2, 0), hz⟩‖ ≤
        2 * ε * ‖Λ ⟨(z.val.1, z.val.2, 0), hz⟩ - ∑ k ∈ K', c k • Λ k‖ := by
  intro ε hε
  let count (z : Zl(χ)) := Nl(χ, s, z)
  let jet (z : Zl(χ)) (m : Fin (count z)) : SpectralLineJetIndex (F := F) χ a s :=
    ⟨(z.val.1, z.val.2, m.val), m.isLt⟩
  let A := spectralConvolution (F := F) a h₀ hs₀(hs) φ
  obtain ⟨i, hi⟩ := h ε hε
  refine ⟨(Finset.Iic i.2).preimage (fun z ↦ (e z).2) hcol.injOn, fun z hzS hz K' c hK' ↦ ?_⟩
  have hzcol : i.2 < (e z).2 := by
    by_contra hcon
    exact hzS (Finset.mem_preimage.mpr (Finset.mem_Iic.mpr (not_lt.mp hcon)))
  have hjet : Injective (jet z) := fun m n hmn ↦ Fin.ext
    (congrArg (fun q : SpectralLineJetIndex (F := F) χ a s ↦ q.val.2.2) hmn)
  have hblock := referee_shell_block A Λ count jet e hcol ε i hi z hzcol
  have hK'' : ∀ k ∈ K', ∀ m, k ≠ jet z m := by
    intro k hk m hkm
    apply hK' k hk
    rw [hkm]
  have hcond := referee_block_conditioning A Λ (count z) (jet z) hjet (2 * ε) hblock
    ⟨0, hz⟩ K' c hK''
  have heig : (Λ (jet z ⟨0, hz⟩)).comp A =
      M(φ, χ z.val.1, shift(0, z.val.2)) • Λ (jet z ⟨0, hz⟩) := by
    ext v
    exact referee_twist_eigen a h₀ hs₀(hs) (Λ (jet z ⟨0, hz⟩)) (χ z.val.1) (shift(0, z.val.2)) _
      (spectralLineJet_memLp χ hs (jet z ⟨0, hz⟩)) (hj (jet z ⟨0, hz⟩))
      (fun g ↦ by
        change spectralZeroJet (χ z.val.1) 0 z.val.2 0 g = _
        unfold spectralZeroJet
        rw [pow_zero, mul_one]) φ v
  rw [heig, referee_norm_smul] at hcond
  exact hcond

#print axioms referee_line_block_bound

/-- Any numbering of the zeros can be replaced by one with the prescribed rows and pairwise
distinct columns. (The same device is used in the certificate posted on issue 6993.) -/
theorem referee_good_enumeration {Z U : Type*} (eχ : U ↪ ℕ) (π : Z → U) (old : Z ↪ ℕ × ℕ) :
    ∃ e : Z ↪ ℕ × ℕ, (∀ z, (e z).1 = eχ (π z)) ∧ Injective (fun z ↦ (e z).2) := by
  let c := old.trans Nat.pairEquiv.toEmbedding
  exact ⟨⟨fun z ↦ (eχ (π z), c z), fun _ _ h ↦ c.injective (congrArg Prod.snd h)⟩,
    fun _ ↦ rfl, c.injective⟩

open Classical in
/-- The same conclusion from the residue lemma as it is quantified: for every numbering
with the prescribed rows. -/
theorem referee_line_block_bound_all (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    {s : ℝ} (hs : 1 < s) (φ : BruhatCompactSupport C𝔽)
    (eχ : PontryaginDual C₁ ↪ ℕ) (e₀ : Zl(χ) ↪ ℕ × ℕ)
    (Λ : SpectralLineJetIndex (F := F) χ a s → StrongDual ℂ Q(a, h₀, hs₀(hs)))
    (hj : ∀ j, spectralSobolevDualEmbedding F a h₀ hs₀(hs) (Λ j) =
      (spectralLineJet_memLp (F := F) χ hs j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) 0 j.val.2.1 j.val.2.2))
    (h : ∀ e : Zl(χ) ↪ ℕ × ℕ, (∀ z, (e z).1 = eχ z.val.1) →
      let box (ij : ℕ × ℕ) :=
        ((Finset.Iic ij.1).product (Finset.Iic ij.2)).preimage e e.injective.injOn
      let jet (z : Zl(χ)) (m : Fin (Nl(χ, s, z))) : SpectralLineJetIndex (F := F) χ a s :=
        ⟨(z.val.1, z.val.2, m.val), m.isLt⟩
      let A := spectralConvolution (F := F) a h₀ hs₀(hs) φ
      ∀ ε > (0 : ℝ), ∃ i, ∀ j ≥ i, ∀ (K : Finset (SpectralLineJetIndex (F := F) χ a s))
        (v : SpectralLineJetIndex (F := F) χ a s → Q(a, h₀, hs₀(hs))),
        (∀ k ∉ K, v k = 0) → ‖∑ k ∈ K, (Λ k).smulRight (v k)‖ ≤ 1 →
        (∑ z ∈ box j \ box i, ∑ m : Fin (Nl(χ, s, z)), Λ (jet z m) (A (v (jet z m)))).re ≤ ε) :
    ∀ ε > (0 : ℝ), ∃ S : Finset Zl(χ), ∀ z ∉ S, ∀ (hz : 0 < Nl(χ, s, z))
      (K' : Finset (SpectralLineJetIndex (F := F) χ a s))
      (c : SpectralLineJetIndex (F := F) χ a s → ℂ),
      (∀ k ∈ K', (k.val.1, k.val.2.1) ≠ z.val) →
      ‖M(φ, χ z.val.1, shift(0, z.val.2))‖ * ‖Λ ⟨(z.val.1, z.val.2, 0), hz⟩‖ ≤
        2 * ε * ‖Λ ⟨(z.val.1, z.val.2, 0), hz⟩ - ∑ k ∈ K', c k • Λ k‖ := by
  obtain ⟨e, he, hcol⟩ := referee_good_enumeration eχ (fun z : Zl(χ) ↦ z.val.1) e₀
  exact referee_line_block_bound a χ hs φ e hcol Λ hj (h e he)

#print axioms referee_line_block_bound_all

open Classical in
/-- The hypothesis `h` of `referee_line_block_bound_all` is literally the library's residue
lemma: this term typechecks. It inherits the `sorry` of that lemma. -/
theorem referee_line_from_library (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice (F := F) χ)
    {s : ℝ} (hs : 1 < s) (φ : BruhatCompactSupport C𝔽)
    (eχ : PontryaginDual C₁ ↪ ℕ) (e₀ : Zl(χ) ↪ ℕ × ℕ)
    (Λ : SpectralLineJetIndex (F := F) χ a s → StrongDual ℂ Q(a, h₀, hs₀(hs)))
    (_hj : ∀ j, spectralSobolevDualEmbedding F a h₀ hs₀(hs) (Λ j) =
      (spectralLineJet_memLp (F := F) χ hs j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) 0 j.val.2.1 j.val.2.2)) :
    ∀ ε > (0 : ℝ), ∃ S : Finset Zl(χ), ∀ z ∉ S, ∀ (hz : 0 < Nl(χ, s, z))
      (K' : Finset (SpectralLineJetIndex (F := F) χ a s))
      (c : SpectralLineJetIndex (F := F) χ a s → ℂ),
      (∀ k ∈ K', (k.val.1, k.val.2.1) ≠ z.val) →
      ‖M(φ, χ z.val.1, shift(0, z.val.2))‖ * ‖Λ ⟨(z.val.1, z.val.2, 0), hz⟩‖ ≤
        2 * ε * ‖Λ ⟨(z.val.1, z.val.2, 0), hz⟩ - ∑ k ∈ K', c k • Λ k‖ :=
  referee_line_block_bound_all a χ hs φ eχ e₀ Λ _hj
    (fun e he ↦ spectralLineConvolution_traceCauchy_scalar_shell (F := F) a χ _hχ hs φ eχ e he Λ _hj)

#print axioms referee_line_from_library

/-! ## Part E: the line estimate as a statement about two zeros (Sobolev exponent above 3) -/

local notation "νl(" s ")" => (μ𝔽 |>.withDensity fun g ↦
  ENNReal.ofReal (intervalSobolevDensity 0 0 s (logIdeleClassNorm F g))⁻¹)
local notation "hms𝔽" => (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.2.2.2.1

omit a in
theorem referee_phase_diff (t u l : ℝ) :
    ‖Complex.exp ((((0 : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I) * (l : ℂ)) -
      Complex.exp ((((0 : ℝ) : ℂ) + ((u : ℝ) : ℂ) * Complex.I) * (l : ℂ))‖ ≤ |t - u| * |l| := by
  have hb : Complex.exp ((((0 : ℝ) : ℂ) + (t : ℂ) * Complex.I) * (l : ℂ)) =
      Complex.exp ((((0 : ℝ) : ℂ) + (u : ℂ) * Complex.I) * (l : ℂ)) *
        Complex.exp (Complex.I * (((t - u) * l : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hb, ← mul_sub_one, norm_mul, Complex.norm_exp]
  have hre : ((((0 : ℝ) : ℂ) + (u : ℂ) * Complex.I) * (l : ℂ)).re = 0 := by simp
  rw [hre, Real.exp_zero, one_mul]
  refine (Real.norm_exp_I_mul_ofReal_sub_one_le (x := (t - u) * l)).trans ?_
  rw [Real.norm_eq_abs, abs_mul]

omit a in
/-- For `s > 3` the log norm is square integrable for the reciprocal line weight. -/
theorem referee_line_log_memLp {s : ℝ} (hs3 : 3 < s) :
    MemLp (fun g : C𝔽 ↦ (logIdeleClassNorm F g : ℂ)) 2 νl(s) := by
  have hl : Continuous (fun g : C𝔽 ↦ (logIdeleClassNorm F g : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuousOn_log.comp_continuous
      (NNReal.continuous_coe.comp (Units.continuous_val.comp
        (isProperMap_ideleClassNorm F).continuous))
      (fun g ↦ NNReal.coe_ne_zero.2 (ideleClassNorm F g).ne_zero))
  have h := spectralLineJet_memLp_of_norm_sq m𝔽 hm𝔽 hms𝔽 μ𝔽 s 1 (by push_cast; linarith) _ hl
    (fun g ↦ by
      change ‖((Real.log ((ideleClassNorm F g).val : ℝ) : ℝ) : ℂ)‖ ^ 2 = _
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_one]
      rfl)
  change MemLp _ 2 ((μ𝔽).withDensity fun g ↦
    ENNReal.ofReal (((1 + (logIdeleClassNorm F g) ^ 2) ^ (s / 2))⁻¹)) at h
  simpa only [intervalSobolevDensity, mul_zero, zero_mul, Real.exp_zero,
    max_self, one_mul] using h

omit a in
/-- The zeroth line jets of one character are Lipschitz in the ordinate, uniformly, in the
reciprocal-weight space. -/
theorem referee_line_jet_lipschitz {s : ℝ} (hs3 : 3 < s) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (η : PontryaginDual C𝔽) (t u : ℝ) (f g : Lp ℂ 2 νl(s)),
      (⇑f =ᵐ[νl(s)] spectralZeroJet (F := F) η 0 t 0) →
      (⇑g =ᵐ[νl(s)] spectralZeroJet (F := F) η 0 u 0) → ‖f - g‖ ≤ B * |t - u| := by
  have hl := referee_line_log_memLp (F := F) hs3
  obtain ⟨L, hL⟩ : ∃ L : Lp ℂ 2 νl(s), ⇑L =ᵐ[νl(s)] fun g ↦ (logIdeleClassNorm F g : ℂ) :=
    ⟨hl.toLp _, MemLp.coeFn_toLp hl⟩
  refine ⟨‖L‖, norm_nonneg _, fun η t u f g hf hg ↦ ?_⟩
  rw [mul_comm]
  apply Lp.norm_le_mul_norm_of_ae_le_mul (g := L)
  filter_upwards [Lp.coeFn_sub f g, hf, hg, hL] with x hsub hfx hgx hLx
  rw [hsub, Pi.sub_apply, hfx, hgx, hLx, Complex.norm_real, Real.norm_eq_abs,
    stripProfile_jet, stripProfile_jet, pow_zero, mul_one, mul_one, ← mul_sub, norm_mul,
    Circle.norm_coe, one_mul]
  exact referee_phase_diff t u (logIdeleClassNorm F x)

#print axioms referee_line_jet_lipschitz

open Classical in
/-- Two zeros of one row. Under the conclusion `h` of the line residue lemma (for every
numbering with the prescribed rows) and Sobolev exponent above 3: for every `ε > 0`, every
zero `z = (ω, t)` outside a finite set and every other zero `z' = (ω, t')` of the same row,
`|M_φ(z)| ‖Λ_{z,0}‖ ≤ 2 ε B |t − t'|`, with `B` depending only on the field and `s`. -/
theorem referee_line_zero_gap (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    {s : ℝ} (hs : 1 < s) (hs3 : 3 < s) (φ : BruhatCompactSupport C𝔽)
    (eχ : PontryaginDual C₁ ↪ ℕ) (e₀ : Zl(χ) ↪ ℕ × ℕ)
    (Λ : SpectralLineJetIndex (F := F) χ a s → StrongDual ℂ Q(a, h₀, hs₀(hs)))
    (hj : ∀ j, spectralSobolevDualEmbedding F a h₀ hs₀(hs) (Λ j) =
      (spectralLineJet_memLp (F := F) χ hs j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) 0 j.val.2.1 j.val.2.2))
    (h : ∀ e : Zl(χ) ↪ ℕ × ℕ, (∀ z, (e z).1 = eχ z.val.1) →
      let box (ij : ℕ × ℕ) :=
        ((Finset.Iic ij.1).product (Finset.Iic ij.2)).preimage e e.injective.injOn
      let jet (z : Zl(χ)) (m : Fin (Nl(χ, s, z))) : SpectralLineJetIndex (F := F) χ a s :=
        ⟨(z.val.1, z.val.2, m.val), m.isLt⟩
      let A := spectralConvolution (F := F) a h₀ hs₀(hs) φ
      ∀ ε > (0 : ℝ), ∃ i, ∀ j ≥ i, ∀ (K : Finset (SpectralLineJetIndex (F := F) χ a s))
        (v : SpectralLineJetIndex (F := F) χ a s → Q(a, h₀, hs₀(hs))),
        (∀ k ∉ K, v k = 0) → ‖∑ k ∈ K, (Λ k).smulRight (v k)‖ ≤ 1 →
        (∑ z ∈ box j \ box i, ∑ m : Fin (Nl(χ, s, z)), Λ (jet z m) (A (v (jet z m)))).re ≤ ε) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ε > (0 : ℝ), ∃ S : Finset Zl(χ), ∀ z ∉ S, ∀ (hz : 0 < Nl(χ, s, z))
      (z' : Zl(χ)) (_hz' : 0 < Nl(χ, s, z')), z'.val.1 = z.val.1 → z' ≠ z →
      ‖M(φ, χ z.val.1, shift(0, z.val.2))‖ * ‖Λ ⟨(z.val.1, z.val.2, 0), hz⟩‖ ≤
        2 * ε * (B * |z.val.2 - z'.val.2|) := by
  obtain ⟨B, hB, hLip⟩ := referee_line_jet_lipschitz (F := F) hs3
  refine ⟨B, hB, fun ε hε ↦ ?_⟩
  obtain ⟨S, hS⟩ := referee_line_block_bound_all a χ hs φ eχ e₀ Λ hj h ε hε
  refine ⟨S, fun z hzS hz z' hz' hrow hne ↦ ?_⟩
  let j : SpectralLineJetIndex (F := F) χ a s := ⟨(z.val.1, z.val.2, 0), hz⟩
  let j' : SpectralLineJetIndex (F := F) χ a s := ⟨(z'.val.1, z'.val.2, 0), hz'⟩
  have hK : ∀ k ∈ ({j'} : Finset (SpectralLineJetIndex (F := F) χ a s)),
      (k.val.1, k.val.2.1) ≠ z.val := by
    intro k hk hkz
    rw [Finset.mem_singleton.mp hk] at hkz
    exact hne (Subtype.ext hkz)
  have hbound := hS z hzS hz {j'} (fun _ ↦ 1) hK
  rw [Finset.sum_singleton, one_smul] at hbound
  have hD := (spectralSobolevDualEmbedding_isometry_range (F := F) a h₀ hs₀(hs)).1
  have hdist : ‖Λ j - Λ j'‖ = ‖(spectralSobolevDualEmbedding F a h₀ hs₀(hs) (Λ j) : Lp ℂ 2 νl(s)) -
      spectralSobolevDualEmbedding F a h₀ hs₀(hs) (Λ j')‖ := by
    have hd := hD.dist_eq (Λ j) (Λ j')
    rw [dist_eq_norm, dist_eq_norm] at hd
    exact hd.symm
  have hf : ⇑(spectralSobolevDualEmbedding F a h₀ hs₀(hs) (Λ j) : Lp ℂ 2 νl(s)) =ᵐ[νl(s)]
      spectralZeroJet (F := F) (χ z.val.1) 0 z.val.2 0 := by
    rw [hj j]
    exact MemLp.coeFn_toLp _
  have hg : ⇑(spectralSobolevDualEmbedding F a h₀ hs₀(hs) (Λ j') : Lp ℂ 2 νl(s)) =ᵐ[νl(s)]
      spectralZeroJet (F := F) (χ z.val.1) 0 z'.val.2 0 := by
    rw [← hrow, hj j']
    exact MemLp.coeFn_toLp _
  have hlip := hLip (χ z.val.1) z.val.2 z'.val.2 _ _ hf hg
  rw [← hdist] at hlip
  exact hbound.trans (mul_le_mul_of_nonneg_left hlip (by positivity))

#print axioms referee_line_zero_gap

omit a in
/-- All unimodular classes of the reciprocal-weight line space have one common positive norm. -/
theorem referee_line_unit_norm {s : ℝ} (hs : 1 < s) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ (f : Lp ℂ 2 νl(s)) (c : C𝔽 → ℂ), (∀ x, ‖c x‖ = 1) →
      ⇑f =ᵐ[νl(s)] c → ‖f‖ = c₀ := by
  have hone : MemLp (fun _ : C𝔽 ↦ (1 : ℂ)) 2 νl(s) := by
    have h := spectralLineJet_memLp_of_norm_sq m𝔽 hm𝔽 hms𝔽 μ𝔽 s 0 (by push_cast; linarith)
      (fun _ ↦ (1 : ℂ)) continuous_const (fun g ↦ by simp)
    change MemLp _ 2 ((μ𝔽).withDensity fun g ↦
      ENNReal.ofReal (((1 + (logIdeleClassNorm F g) ^ 2) ^ (s / 2))⁻¹)) at h
    simpa only [intervalSobolevDensity, mul_zero, zero_mul, Real.exp_zero,
      max_self, one_mul] using h
  obtain ⟨u, hu⟩ : ∃ u : Lp ℂ 2 νl(s), ⇑u =ᵐ[νl(s)] fun _ ↦ (1 : ℂ) :=
    ⟨hone.toLp _, MemLp.coeFn_toLp hone⟩
  have heq (f : Lp ℂ 2 νl(s)) (c : C𝔽 → ℂ) (hc : ∀ x, ‖c x‖ = 1) (hf : ⇑f =ᵐ[νl(s)] c) :
      ‖f‖ = ‖u‖ := by
    have he : ∀ᵐ x ∂νl(s), ‖f x‖ = ‖u x‖ := by
      filter_upwards [hf, hu] with x h₁ h₂
      rw [h₁, h₂, hc x, norm_one]
    exact le_antisymm (Lp.norm_le_norm_of_ae_le (he.mono fun _ h ↦ h.le))
      (Lp.norm_le_norm_of_ae_le (he.mono fun _ h ↦ h.ge))
  refine ⟨‖u‖, ?_, heq⟩
  rw [norm_pos_iff]
  intro hu0
  have hfalse : ∀ᵐ x ∂νl(s), False := by
    filter_upwards [hu, Lp.coeFn_zero ℂ 2 νl(s)] with x h₁ h₂
    rw [hu0, h₂] at h₁
    exact zero_ne_one h₁
  have hν : νl(s) = 0 := ae_eq_bot.mp (eventually_false_iff_eq_bot.mp hfalse)
  let w (g : C𝔽) := intervalSobolevDensity 0 0 s (logIdeleClassNorm F g)
  have hw : Measurable w := by
    have hD : Continuous (intervalSobolevDensity 0 0 s) := by
      unfold intervalSobolevDensity
      fun_prop
    exact hD.measurable.comp ((NNReal.continuous_coe.comp
      (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous)).measurable.log)
  have habs : μ𝔽 ≪ (μ𝔽).withDensity (fun g ↦ ENNReal.ofReal (w g)⁻¹) := by
    refine withDensity_absolutelyContinuous' hw.inv.ennreal_ofReal.aemeasurable (.of_forall fun g ↦ ?_)
    refine ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr ?_)
    exact mul_pos (lt_max_of_lt_left (Real.exp_pos _)) (Real.rpow_pos_of_pos (by positivity) _)
  have hμ : μ𝔽 univ = 0 := habs (by
    rw [show (μ𝔽).withDensity (fun g ↦ ENNReal.ofReal (w g)⁻¹) = 0 from hν]
    rfl)
  exact (isOpen_univ.measure_ne_zero μ𝔽 univ_nonempty) hμ

omit a in
theorem referee_line_jet_norm_one (η : PontryaginDual C𝔽) (t : ℝ) (x : C𝔽) :
    ‖spectralZeroJet (F := F) η 0 t 0 x‖ = 1 := by
  rw [stripProfile_jet, pow_zero, mul_one, norm_mul, Circle.norm_coe, one_mul, Complex.norm_exp]
  have hre : ((((0 : ℝ) : ℂ) + (t : ℂ) * Complex.I) * (logIdeleClassNorm F x : ℂ)).re = 0 := by
    simp
  rw [hre, Real.exp_zero]

open Classical in
/-- The line residue lemma as a statement about zeros and Mellin values only. With Sobolev
exponent above 3 and the conclusion `h` of the residue lemma for every numbering with the
prescribed rows: there is `κ`, depending only on the field and `s`, such that for every
`ε > 0`, every zero `(ω, t)` outside a finite set and every other zero `(ω, t')` of the
same row, `|M_φ(χ_ω, i t)| ≤ ε κ |t − t'|`. -/
theorem referee_line_mellin_gap (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    {s : ℝ} (hs : 1 < s) (hs3 : 3 < s) (φ : BruhatCompactSupport C𝔽)
    (eχ : PontryaginDual C₁ ↪ ℕ) (e₀ : Zl(χ) ↪ ℕ × ℕ)
    (Λ : SpectralLineJetIndex (F := F) χ a s → StrongDual ℂ Q(a, h₀, hs₀(hs)))
    (hj : ∀ j, spectralSobolevDualEmbedding F a h₀ hs₀(hs) (Λ j) =
      (spectralLineJet_memLp (F := F) χ hs j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) 0 j.val.2.1 j.val.2.2))
    (h : ∀ e : Zl(χ) ↪ ℕ × ℕ, (∀ z, (e z).1 = eχ z.val.1) →
      let box (ij : ℕ × ℕ) :=
        ((Finset.Iic ij.1).product (Finset.Iic ij.2)).preimage e e.injective.injOn
      let jet (z : Zl(χ)) (m : Fin (Nl(χ, s, z))) : SpectralLineJetIndex (F := F) χ a s :=
        ⟨(z.val.1, z.val.2, m.val), m.isLt⟩
      let A := spectralConvolution (F := F) a h₀ hs₀(hs) φ
      ∀ ε > (0 : ℝ), ∃ i, ∀ j ≥ i, ∀ (K : Finset (SpectralLineJetIndex (F := F) χ a s))
        (v : SpectralLineJetIndex (F := F) χ a s → Q(a, h₀, hs₀(hs))),
        (∀ k ∉ K, v k = 0) → ‖∑ k ∈ K, (Λ k).smulRight (v k)‖ ≤ 1 →
        (∑ z ∈ box j \ box i, ∑ m : Fin (Nl(χ, s, z)), Λ (jet z m) (A (v (jet z m)))).re ≤ ε) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ ε > (0 : ℝ), ∃ S : Finset Zl(χ), ∀ z ∉ S, 0 < Nl(χ, s, z) →
      ∀ z' : Zl(χ), 0 < Nl(χ, s, z') → z'.val.1 = z.val.1 → z' ≠ z →
      ‖M(φ, χ z.val.1, shift(0, z.val.2))‖ ≤ ε * κ * |z.val.2 - z'.val.2| := by
  obtain ⟨B, hB, hgap⟩ := referee_line_zero_gap a χ hs hs3 φ eχ e₀ Λ hj h
  obtain ⟨c₀, hc₀, hunit⟩ := referee_line_unit_norm (F := F) hs
  refine ⟨2 * B / c₀, by positivity, fun ε hε ↦ ?_⟩
  obtain ⟨S, hS⟩ := hgap ε hε
  refine ⟨S, fun z hzS hz z' hz' hrow hne ↦ ?_⟩
  have hbound := hS z hzS hz z' hz' hrow hne
  let j : SpectralLineJetIndex (F := F) χ a s := ⟨(z.val.1, z.val.2, 0), hz⟩
  have hD := (spectralSobolevDualEmbedding_isometry_range (F := F) a h₀ hs₀(hs)).1
  have hnorm : ‖Λ j‖ = ‖(spectralSobolevDualEmbedding F a h₀ hs₀(hs) (Λ j) : Lp ℂ 2 νl(s))‖ := by
    have hd := hD.dist_eq (Λ j) 0
    rw [dist_eq_norm, dist_eq_norm, map_zero, sub_zero, sub_zero] at hd
    exact hd.symm
  have hf : ⇑(spectralSobolevDualEmbedding F a h₀ hs₀(hs) (Λ j) : Lp ℂ 2 νl(s)) =ᵐ[νl(s)]
      spectralZeroJet (F := F) (χ z.val.1) 0 z.val.2 0 := by
    rw [hj j]
    exact MemLp.coeFn_toLp _
  have hc : ‖Λ j‖ = c₀ :=
    hnorm.trans (hunit _ _ (referee_line_jet_norm_one (χ z.val.1) z.val.2) hf)
  change _ * ‖Λ j‖ ≤ _ at hbound
  rw [hc] at hbound
  have hfin : ε * (2 * B / c₀) * |z.val.2 - z'.val.2| = 2 * ε * (B * |z.val.2 - z'.val.2|) / c₀ := by
    ring
  rw [hfin, le_div_iff₀ hc₀]
  exact hbound

#print axioms referee_line_mellin_gap

end Line

/-! ## Part F: the strip residue lemma at width zero, as a statement about zeros and Mellin
values only (Sobolev exponent above 3) -/

section StripZeroWidth

variable (a : ℝ)

local notation "Zs(" χ ", " α ")" => {z : PontryaginDual C₁ × ℝ × ℝ //
  z.2.1 ∈ Icc (-α) α ∧ 0 < order(χ z.1, shift(a + z.2.1, z.2.2))}
local notation "Ns(" χ ", " α ", " s ", " z ")" => spectralStripMultiplicity α s (z).val.2.1
  (mult(χ (z).val.1, shift(a + (z).val.2.1, (z).val.2.2)))
local notation "νs(" l ", " r ", " s ")" => (μ𝔽 |>.withDensity fun g ↦
  ENNReal.ofReal (intervalSobolevDensity l r s (logIdeleClassNorm F g))⁻¹)

omit a in
/-- `referee_line_jet_lipschitz` for a base interval whose endpoints are both zero. -/
theorem referee_jet_lipschitz_gen {l r s : ℝ} (hl : l = 0) (hr : r = 0) (hs3 : 3 < s) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (η : PontryaginDual C𝔽) (t u : ℝ) (f g : Lp ℂ 2 νs(l, r, s)),
      (⇑f =ᵐ[νs(l, r, s)] spectralZeroJet (F := F) η 0 t 0) →
      (⇑g =ᵐ[νs(l, r, s)] spectralZeroJet (F := F) η 0 u 0) → ‖f - g‖ ≤ B * |t - u| := by
  subst hl hr
  exact referee_line_jet_lipschitz (F := F) hs3

omit a in
/-- `referee_line_unit_norm` for a base interval whose endpoints are both zero. -/
theorem referee_unit_norm_gen {l r s : ℝ} (hl : l = 0) (hr : r = 0) (hs : 1 < s) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ (f : Lp ℂ 2 νs(l, r, s)) (c : C𝔽 → ℂ), (∀ x, ‖c x‖ = 1) →
      ⇑f =ᵐ[νs(l, r, s)] c → ‖f‖ = c₀ := by
  subst hl hr
  exact referee_line_unit_norm (F := F) hs

/-- Width zero. Under the conclusion `h` of the strip residue lemma for one test, with strip
width zero and Sobolev exponent above 3, there is one constant `c` such that any two distinct
zeros `(ω, 0, t)` and `(ω, 0, t')` of one row with surviving zeroth jets satisfy
`|M_φ(χ_ω, i t)| ≤ c |t − t'|`. -/
theorem referee_strip_zero_width_mellin_gap (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    {α s : ℝ} (hα : 0 ≤ α) (hα0 : α = 0) (hs : 1 < s) (hs3 : 3 < s)
    (φ : BruhatCompactSupport C𝔽)
    (x : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s → Q(a, hStrip(hα), hs₀(hs)))
    (Λ : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s → StrongDual ℂ Q(a, hStrip(hα), hs₀(hs)))
    (hb : IsSpectralMarkushevichBasis x Λ)
    (hj : ∀ j, spectralSobolevDualEmbedding F a hStrip(hα) hs₀(hs) (Λ j) =
      (spectralStripJet_memLp (F := F) (fun ω ↦ χ ω) hα hs₀(hs) j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2))
    (h : let H := Q(a, hStrip(hα), hs₀(hs))
      let A := spectralConvolution (F := F) a hStrip(hα) hs₀(hs) φ
      let jet (z : Zs(χ, α)) (m : Fin (Ns(χ, α, s, z))) :
          SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s :=
        ⟨(z.val.1, z.val.2.1, z.val.2.2, m.val), m.isLt⟩
      ∀ U : compactOperator (RingHom.id ℂ) H H,
        Summable (fun z : Zs(χ, α) ↦ ∑ m, Λ (jet z m) (A (U.val (x (jet z m)))))) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ z z' : Zs(χ, α), 0 < Ns(χ, α, s, z) → 0 < Ns(χ, α, s, z') →
      z'.val.1 = z.val.1 → z' ≠ z →
      ‖M(φ, χ z.val.1, shift(0, z.val.2.2))‖ ≤ c * |z.val.2.2 - z'.val.2.2| := by
  obtain ⟨c, hc⟩ := referee_strip_two_zero a χ hα hs φ x Λ hb hj h
  have hl0 : -α = 0 := by rw [hα0, neg_zero]
  obtain ⟨B, hB, hLip⟩ := referee_jet_lipschitz_gen (F := F) (l := -α) (r := α) (s := s)
    hl0 hα0 hs3
  obtain ⟨c₀, hc₀, hunit⟩ := referee_unit_norm_gen (F := F) (l := -α) (r := α) (s := s)
    hl0 hα0 hs
  refine ⟨max c 0 * B / c₀, by positivity, fun z z' hz hz' hrow hne ↦ ?_⟩
  have hβ : z.val.2.1 = 0 := by
    have h₁ : -α ≤ z.val.2.1 := z.property.1.1
    have h₂ : z.val.2.1 ≤ α := z.property.1.2
    exact le_antisymm (by linarith) (by linarith)
  have hβ' : z'.val.2.1 = 0 := by
    have h₁ : -α ≤ z'.val.2.1 := z'.property.1.1
    have h₂ : z'.val.2.1 ≤ α := z'.property.1.2
    exact le_antisymm (by linarith) (by linarith)
  let j : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s :=
    ⟨(z.val.1, z.val.2.1, z.val.2.2, 0), hz⟩
  let j' : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s :=
    ⟨(z'.val.1, z'.val.2.1, z'.val.2.2, 0), hz'⟩
  have hkne : (j'.val.1, j'.val.2.1, j'.val.2.2.1) ≠ z.val := fun hEq ↦ hne (Subtype.ext hEq)
  have hbound : ‖M(φ, χ z.val.1, shift(z.val.2.1, z.val.2.2))‖ * ‖Λ j‖ ≤ c * ‖Λ j - Λ j'‖ :=
    hc z hz j' hkne
  have hD := (spectralSobolevDualEmbedding_isometry_range (F := F) a hStrip(hα) hs₀(hs)).1
  have hdist : ‖Λ j - Λ j'‖ =
      ‖(spectralSobolevDualEmbedding F a hStrip(hα) hs₀(hs) (Λ j) : Lp ℂ 2 νs(-α, α, s)) -
        spectralSobolevDualEmbedding F a hStrip(hα) hs₀(hs) (Λ j')‖ := by
    have hd := hD.dist_eq (Λ j) (Λ j')
    rw [dist_eq_norm, dist_eq_norm] at hd
    exact hd.symm
  have hnorm : ‖Λ j‖ =
      ‖(spectralSobolevDualEmbedding F a hStrip(hα) hs₀(hs) (Λ j) : Lp ℂ 2 νs(-α, α, s))‖ := by
    have hd := hD.dist_eq (Λ j) 0
    rw [dist_eq_norm, dist_eq_norm, map_zero, sub_zero, sub_zero] at hd
    exact hd.symm
  have hf : ⇑(spectralSobolevDualEmbedding F a hStrip(hα) hs₀(hs) (Λ j) : Lp ℂ 2 νs(-α, α, s))
      =ᵐ[νs(-α, α, s)] spectralZeroJet (F := F) (χ z.val.1) 0 z.val.2.2 0 := by
    rw [hj j]
    have hE : spectralZeroJet (F := F) (χ z.val.1) z.val.2.1 z.val.2.2 0 =
        spectralZeroJet (F := F) (χ z.val.1) 0 z.val.2.2 0 := by rw [hβ]
    exact (MemLp.coeFn_toLp _).trans (Filter.EventuallyEq.of_eq hE)
  have hg : ⇑(spectralSobolevDualEmbedding F a hStrip(hα) hs₀(hs) (Λ j') : Lp ℂ 2 νs(-α, α, s))
      =ᵐ[νs(-α, α, s)] spectralZeroJet (F := F) (χ z.val.1) 0 z'.val.2.2 0 := by
    rw [hj j']
    have hE : spectralZeroJet (F := F) (χ z'.val.1) z'.val.2.1 z'.val.2.2 0 =
        spectralZeroJet (F := F) (χ z.val.1) 0 z'.val.2.2 0 := by rw [hβ', hrow]
    exact (MemLp.coeFn_toLp _).trans (Filter.EventuallyEq.of_eq hE)
  have hlip := hLip (χ z.val.1) z.val.2.2 z'.val.2.2 _ _ hf hg
  rw [← hdist] at hlip
  have hc₁ : ‖Λ j‖ = c₀ :=
    hnorm.trans (hunit _ _ (referee_line_jet_norm_one (χ z.val.1) z.val.2.2) hf)
  have hM : M(φ, χ z.val.1, shift(z.val.2.1, z.val.2.2)) =
      M(φ, χ z.val.1, shift(0, z.val.2.2)) := by rw [hβ]
  rw [hc₁, hM] at hbound
  have hstep : c * ‖Λ j - Λ j'‖ ≤ max c 0 * (B * |z.val.2.2 - z'.val.2.2|) :=
    (mul_le_mul_of_nonneg_right (le_max_left c 0) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hlip (le_max_right c 0))
  have hfin : max c 0 * B / c₀ * |z.val.2.2 - z'.val.2.2| =
      max c 0 * (B * |z.val.2.2 - z'.val.2.2|) / c₀ := by ring
  rw [hfin, le_div_iff₀ hc₀]
  exact hbound.trans hstep

#print axioms referee_strip_zero_width_mellin_gap

/-- The hypothesis `h` of `referee_strip_zero_width_mellin_gap` is literally the conclusion of
the library's strip residue lemma: this term typechecks. It inherits the `sorry` of that
lemma. -/
theorem referee_strip_zero_width_from_library (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω))
    {α s : ℝ} (hα : 0 ≤ α) (hα0 : α = 0) (hs : 1 < s) (hs3 : 3 < s)
    (φ : BruhatCompactSupport C𝔽)
    (x : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s → Q(a, hStrip(hα), hs₀(hs)))
    (Λ : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s → StrongDual ℂ Q(a, hStrip(hα), hs₀(hs)))
    (_hb : IsSpectralMarkushevichBasis x Λ)
    (_hj : ∀ j, spectralSobolevDualEmbedding F a hStrip(hα) hs₀(hs) (Λ j) =
      (spectralStripJet_memLp (F := F) (fun ω ↦ χ ω) hα hs₀(hs) j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2)) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ z z' : Zs(χ, α), 0 < Ns(χ, α, s, z) → 0 < Ns(χ, α, s, z') →
      z'.val.1 = z.val.1 → z' ≠ z →
      ‖M(φ, χ z.val.1, shift(0, z.val.2.2))‖ ≤ c * |z.val.2.2 - z'.val.2.2| :=
  referee_strip_zero_width_mellin_gap a χ hα hα0 hs hs3 φ x Λ _hb _hj
    (spectralStripConvolution_traceCauchy_compact_block_series a χ _hχ hα hs φ x Λ _hb _hj)

#print axioms referee_strip_zero_width_from_library

end StripZeroWidth

/-! ## Part G: uniformity over radial tests with Schwartz profiles (width zero) -/

section Uniform

open scoped SchwartzMap

variable (a : ℝ)

local notation "Zs(" χ ", " α ")" => {z : PontryaginDual C₁ × ℝ × ℝ //
  z.2.1 ∈ Icc (-α) α ∧ 0 < order(χ z.1, shift(a + z.2.1, z.2.2))}
local notation "Ns(" χ ", " α ", " s ", " z ")" => spectralStripMultiplicity α s (z).val.2.1
  (mult(χ (z).val.1, shift(a + (z).val.2.1, (z).val.2.2)))
local notation "hms𝔽" => (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.2.2.2.1

omit a in
/-- A smooth compactly supported cutoff times a Schwartz profile is a test on the real line. -/
theorem referee_profile_mem (θ : ℝ → ℝ) (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (hθc : HasCompactSupport θ)
    (f : 𝓢(ℝ, ℂ)) :
    (fun y : Multiplicative ℝ ↦ (θ y.toAdd : ℂ) * f y.toAdd) ∈
      bruhatCompactSupportSubmodule (Multiplicative ℝ) := by
  rw [mem_bruhatCompactSupportSubmodule_real_iff]
  constructor
  · change ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ ↦ (θ x : ℂ) * f x)
    exact (Complex.ofRealCLM.contDiff.comp hθ).mul (f.smooth ⊤)
  · change HasCompactSupport (fun x : ℝ ↦ (θ x : ℂ) * f x)
    exact (hθc.comp_left Complex.ofReal_zero).mul_right

omit a in
/-- The cutoff alone is a test on the real line. -/
theorem referee_cutoff_mem (θ : ℝ → ℝ) (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (hθc : HasCompactSupport θ) :
    (fun y : Multiplicative ℝ ↦ (θ y.toAdd : ℂ)) ∈
      bruhatCompactSupportSubmodule (Multiplicative ℝ) := by
  rw [mem_bruhatCompactSupportSubmodule_real_iff]
  constructor
  · change ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ ↦ (θ x : ℂ))
    exact Complex.ofRealCLM.contDiff.comp hθ
  · change HasCompactSupport (fun x : ℝ ↦ (θ x : ℂ))
    exact hθc.comp_left Complex.ofReal_zero

omit a in
/-- The radial test `x ↦ conj(η x) θ(log|x|) f(log|x|)` on the idele class group. -/
def refereeRadialTest (η : PontryaginDual C𝔽) (θ : ℝ → ℝ) (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (hθc : HasCompactSupport θ) (f : 𝓢(ℝ, ℂ)) : BruhatCompactSupport C𝔽 :=
  ⟨fun x : C𝔽 ↦ ((η⁻¹ x : Circle) : ℂ) *
      (⟨_, referee_profile_mem θ hθ hθc f⟩ : BruhatCompactSupport (Multiplicative ℝ)).val
        (positiveRealLogEquiv (m𝔽 x)),
    spectralHomogeneousTest_lift_mem (F := F) hms𝔽 η⁻¹ ⟨_, referee_profile_mem θ hθ hθc f⟩⟩

omit a in
theorem refereeRadialTest_val (η : PontryaginDual C𝔽) (θ : ℝ → ℝ) (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (hθc : HasCompactSupport θ) (f : 𝓢(ℝ, ℂ)) (x : C𝔽) :
    (refereeRadialTest (F := F) η θ hθ hθc f).val x = ((η⁻¹ x : Circle) : ℂ) *
      ((θ (positiveRealLogEquiv (m𝔽 x)).toAdd : ℂ) * f (positiveRealLogEquiv (m𝔽 x)).toAdd) :=
  rfl

omit a in
/-- The Mellin value of the radial test at a fixed twist is a continuous linear functional of
the Schwartz profile. -/
theorem referee_radial_mellin_clm (η : PontryaginDual C𝔽) (θ : ℝ → ℝ) (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (hθc : HasCompactSupport θ) (w : ℂ) :
    ∃ E : 𝓢(ℝ, ℂ) →L[ℂ] ℂ, ∀ f, E f = M(refereeRadialTest (F := F) η θ hθ hθc f, η, w) := by
  let tw := ideleClassNormTwist (F := F) η w
  let T (f : 𝓢(ℝ, ℂ)) := refereeRadialTest (F := F) η θ hθ hθc f
  let A (f : 𝓢(ℝ, ℂ)) : ℂ := M(T f, η, w)
  have hval (f : 𝓢(ℝ, ℂ)) : A f = ∫ g, (T f).val g * tw g ∂μ𝔽 :=
    (spectralConvolution_mellin_integrable (T f) η w).2
  have hint (f : 𝓢(ℝ, ℂ)) : Integrable (fun g ↦ (T f).val g * tw g) μ𝔽 :=
    (spectralConvolution_mellin_integrable (T f) η w).1
  let Θ : BruhatCompactSupport C𝔽 :=
    ⟨fun x : C𝔽 ↦ ((η⁻¹ x : Circle) : ℂ) *
        (⟨_, referee_cutoff_mem θ hθ hθc⟩ : BruhatCompactSupport (Multiplicative ℝ)).val
          (positiveRealLogEquiv (m𝔽 x)),
      spectralHomogeneousTest_lift_mem (F := F) hms𝔽 η⁻¹ ⟨_, referee_cutoff_mem θ hθ hθc⟩⟩
  have hΘ : Integrable (fun g ↦ Θ.val g * tw g) μ𝔽 :=
    (spectralConvolution_mellin_integrable Θ η w).1
  have hfac (f : 𝓢(ℝ, ℂ)) (g : C𝔽) : (T f).val g * tw g =
      (Θ.val g * tw g) * f (positiveRealLogEquiv (m𝔽 g)).toAdd := by
    change ((η⁻¹ g : Circle) : ℂ) * ((θ (positiveRealLogEquiv (m𝔽 g)).toAdd : ℂ) *
      f (positiveRealLogEquiv (m𝔽 g)).toAdd) * tw g =
      (((η⁻¹ g : Circle) : ℂ) * (θ (positiveRealLogEquiv (m𝔽 g)).toAdd : ℂ) * tw g) *
        f (positiveRealLogEquiv (m𝔽 g)).toAdd
    ring
  have hadd (f g : 𝓢(ℝ, ℂ)) : A (f + g) = A f + A g := by
    rw [hval, hval, hval, ← integral_add (hint f) (hint g)]
    refine integral_congr_ae (.of_forall fun y ↦ ?_)
    change (T (f + g)).val y * tw y = (T f).val y * tw y + (T g).val y * tw y
    rw [hfac, hfac, hfac]
    change _ * (f (positiveRealLogEquiv (m𝔽 y)).toAdd + g (positiveRealLogEquiv (m𝔽 y)).toAdd) = _
    ring
  have hsmul (c : ℂ) (f : 𝓢(ℝ, ℂ)) : A (c • f) = (RingHom.id ℂ) c • A f := by
    rw [RingHom.id_apply, smul_eq_mul, hval, hval, ← integral_const_mul]
    refine integral_congr_ae (.of_forall fun y ↦ ?_)
    change (T (c • f)).val y * tw y = c * ((T f).val y * tw y)
    rw [hfac, hfac]
    change _ * (c * f (positiveRealLogEquiv (m𝔽 y)).toAdd) = _
    ring
  have hbound : ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ f : 𝓢(ℝ, ℂ),
      ‖A f‖ ≤ C * S.sup (schwartzSeminormFamily ℂ ℝ ℂ) f := by
    refine ⟨{(0, 0)}, ∫ g, ‖Θ.val g * tw g‖ ∂μ𝔽, integral_nonneg fun _ ↦ norm_nonneg _,
      fun f ↦ ?_⟩
    rw [Finset.sup_singleton, SchwartzMap.schwartzSeminormFamily_apply, hval, ← integral_mul_const]
    refine norm_integral_le_of_norm_le (hΘ.norm.mul_const _) (.of_forall fun g ↦ ?_)
    rw [hfac, norm_mul]
    exact mul_le_mul_of_nonneg_left (SchwartzMap.norm_le_seminorm ℂ f _) (norm_nonneg _)
  exact ⟨SchwartzMap.mkCLMtoNormedSpace (𝕜 := ℂ) (σ := RingHom.id ℂ) A hadd hsmul hbound,
    fun f ↦ rfl⟩

#print axioms referee_radial_mellin_clm

/-- Width zero, all radial tests of one row at once. Suppose the conclusion of the strip
residue lemma holds for every test (strip width zero, Sobolev exponent above 3). Fix a row `ω`
and a smooth compactly supported cutoff `θ`. Then there are finitely many Schwartz seminorms
and a constant `C` such that for every Schwartz profile `f` and any two distinct zeros
`(ω, 0, t)`, `(ω, 0, t')` of that row with surviving zeroth jets, the Mellin value at `i t` of
the radial test `x ↦ conj(χ_ω x) θ(log|x|) f(log|x|)` is at most
`C · (sup of the seminorms)(f) · |t − t'|`. -/
theorem referee_strip_zero_width_uniform (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    {α s : ℝ} (hα : 0 ≤ α) (hα0 : α = 0) (hs : 1 < s) (hs3 : 3 < s)
    (x : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s → Q(a, hStrip(hα), hs₀(hs)))
    (Λ : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s → StrongDual ℂ Q(a, hStrip(hα), hs₀(hs)))
    (hb : IsSpectralMarkushevichBasis x Λ)
    (hj : ∀ j, spectralSobolevDualEmbedding F a hStrip(hα) hs₀(hs) (Λ j) =
      (spectralStripJet_memLp (F := F) (fun ω ↦ χ ω) hα hs₀(hs) j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2))
    (θ : ℝ → ℝ) (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (hθc : HasCompactSupport θ)
    (ω : PontryaginDual C₁)
    (h : ∀ φ : BruhatCompactSupport C𝔽,
      let H := Q(a, hStrip(hα), hs₀(hs))
      let A := spectralConvolution (F := F) a hStrip(hα) hs₀(hs) φ
      let jet (z : Zs(χ, α)) (m : Fin (Ns(χ, α, s, z))) :
          SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s :=
        ⟨(z.val.1, z.val.2.1, z.val.2.2, m.val), m.isLt⟩
      ∀ U : compactOperator (RingHom.id ℂ) H H,
        Summable (fun z : Zs(χ, α) ↦ ∑ m, Λ (jet z m) (A (U.val (x (jet z m)))))) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ (f : 𝓢(ℝ, ℂ)) (z z' : Zs(χ, α)),
      0 < Ns(χ, α, s, z) → 0 < Ns(χ, α, s, z') → z.val.1 = ω → z'.val.1 = ω → z' ≠ z →
      ‖M(refereeRadialTest (F := F) (χ ω) θ hθ hθc f, χ ω, shift(0, z.val.2.2))‖ ≤
        C * (S.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f * |z.val.2.2 - z'.val.2.2| := by
  classical
  have hcomplete : CompleteSpace 𝓢(ℝ, ℂ) := completeSpace_schwartzMap
  have hcount : (uniformity 𝓢(ℝ, ℂ)).IsCountablyGenerated := by
    rw [uniformity_eq_comap_nhds_zero 𝓢(ℝ, ℂ)]
    infer_instance
  have hbaire : BaireSpace 𝓢(ℝ, ℂ) := BaireSpace.of_completelyPseudoMetrizable
  let ι := {p : Zs(χ, α) × Zs(χ, α) // 0 < Ns(χ, α, s, p.1) ∧ 0 < Ns(χ, α, s, p.2) ∧
    p.1.val.1 = ω ∧ p.2.val.1 = ω ∧ p.2 ≠ p.1}
  choose E hE using fun t : ℝ ↦
    referee_radial_mellin_clm (F := F) (χ ω) θ hθ hθc (shift(0, t))
  let d (i : ι) : ℝ := |i.val.1.val.2.2 - i.val.2.val.2.2|
  let p (i : ι) : Seminorm ℂ 𝓢(ℝ, ℂ) :=
    (normSeminorm ℂ ℂ).comp ((((d i)⁻¹ : ℝ) : ℂ) • E i.val.1.val.2.2).toLinearMap
  have hp_apply (i : ι) (f : 𝓢(ℝ, ℂ)) : p i f = (d i)⁻¹ * ‖E i.val.1.val.2.2 f‖ := by
    change ‖(((d i)⁻¹ : ℝ) : ℂ) • E i.val.1.val.2.2 f‖ = _
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr (abs_nonneg _))]
  have hpc (i : ι) : Continuous (p i) := by
    change Continuous fun f ↦ ‖((((d i)⁻¹ : ℝ) : ℂ) • E i.val.1.val.2.2) f‖
    exact continuous_norm.comp (ContinuousLinearMap.continuous _)
  have hpoint (f : 𝓢(ℝ, ℂ)) : ∃ c : ℝ, 0 ≤ c ∧ ∀ (z z' : Zs(χ, α)),
      0 < Ns(χ, α, s, z) → 0 < Ns(χ, α, s, z') → z.val.1 = ω → z'.val.1 = ω → z' ≠ z →
      ‖E z.val.2.2 f‖ ≤ c * |z.val.2.2 - z'.val.2.2| := by
    obtain ⟨c, hc0, hc⟩ := referee_strip_zero_width_mellin_gap a χ hα hα0 hs hs3
      (refereeRadialTest (F := F) (χ ω) θ hθ hθc f) x Λ hb hj (h _)
    refine ⟨c, hc0, fun z z' hz hz' hzω hz'ω hne ↦ ?_⟩
    have hmain := hc z z' hz hz' (hz'ω.trans hzω.symm) hne
    rw [hzω] at hmain
    rw [hE]
    exact hmain
  have hbdd : BddAbove (range p) := by
    rw [Seminorm.bddAbove_range_iff]
    intro f
    obtain ⟨c, hc0, hc⟩ := hpoint f
    refine ⟨c, ?_⟩
    rintro _ ⟨i, rfl⟩
    change p i f ≤ c
    rw [hp_apply]
    have hbi := hc i.val.1 i.val.2 i.property.1 i.property.2.1 i.property.2.2.1
      i.property.2.2.2.1 i.property.2.2.2.2
    by_cases hd : d i = 0
    · rw [hd, inv_zero, zero_mul]
      exact hc0
    · have hdpos : 0 < d i := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hd)
      rw [inv_mul_le_iff₀ hdpos, mul_comm]
      exact hbi
  have hcont : Continuous ⇑(⨆ i, p i) := by
    rw [Seminorm.coe_iSup_eq hbdd]
    exact Seminorm.continuous_iSup p hpc hbdd
  obtain ⟨S, C, -, hC⟩ :=
    Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ ℝ ℂ) (⨆ i, p i) hcont
  refine ⟨S, C, C.coe_nonneg, fun f z z' hz hz' hzω hz'ω hne ↦ ?_⟩
  let i : ι := ⟨(z, z'), hz, hz', hzω, hz'ω, hne⟩
  have h1 : p i f ≤ (C • S.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f :=
    (Seminorm.le_def.mp (le_ciSup hbdd i) f).trans (Seminorm.le_def.mp hC f)
  rw [hp_apply] at h1
  have h2 : (C • S.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f =
      (C : ℝ) * (S.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f := rfl
  rw [h2] at h1
  rw [← hE]
  obtain ⟨c, hc0, hc⟩ := hpoint f
  have hbz := hc z z' hz hz' hzω hz'ω hne
  have hdi : d i = |z.val.2.2 - z'.val.2.2| := rfl
  by_cases hd : d i = 0
  · rw [← hdi, hd, mul_zero] at hbz ⊢
    exact hbz
  · have hdpos : 0 < d i := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hd)
    rw [inv_mul_le_iff₀ hdpos] at h1
    rw [← hdi, mul_comm]
    exact h1

#print axioms referee_strip_zero_width_uniform

/-! ### Modulated profiles: from the seminorm bound to a polynomial lower bound for gaps -/

omit a in
theorem referee_iteratedDeriv_cexp (c : ℂ) (n : ℕ) :
    iteratedDeriv n (fun x : ℝ ↦ Complex.exp (c * (x : ℂ))) =
      fun x : ℝ ↦ c ^ n * Complex.exp (c * (x : ℂ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    have h1 : HasDerivAt (fun y : ℝ ↦ (y : ℂ)) 1 x := by
      simpa using (hasDerivAt_id x).ofReal_comp
    have h : HasDerivAt (fun y : ℝ ↦ c ^ n * Complex.exp (c * (y : ℂ)))
        (c ^ n * (Complex.exp (c * (x : ℂ)) * (c * 1))) x :=
      ((h1.const_mul c).cexp).const_mul (c ^ n)
    rw [h.deriv]
    ring

omit a in
theorem referee_iteratedDeriv_cexp_apply (c : ℂ) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun x : ℝ ↦ Complex.exp (c * (x : ℂ))) x =
      c ^ n * Complex.exp (c * (x : ℂ)) := by
  rw [referee_iteratedDeriv_cexp]

omit a in
/-- A compactly supported Schwartz profile modulated by `e^{-itx}` is a Schwartz function
whose seminorms grow at most polynomially in `t`. -/
theorem referee_modulated_profile (ψ : 𝓢(ℝ, ℂ)) (hψc : HasCompactSupport ψ) (t : ℝ) :
    ∃ f : 𝓢(ℝ, ℂ), (∀ x : ℝ, f x = Complex.exp (-(t * Complex.I) * (x : ℂ)) * ψ x) ∧
      ∀ k n : ℕ, SchwartzMap.seminorm ℂ k n f ≤ (1 + |t|) ^ n *
        ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * SchwartzMap.seminorm ℂ k (n - i) ψ := by
  let c : ℂ := -(t * Complex.I)
  have he : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ ↦ Complex.exp (c * (x : ℂ))) :=
    (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ ↦ Complex.exp (c * (x : ℂ)) * ψ x) :=
    he.mul (ψ.smooth ⊤)
  have hcs : HasCompactSupport (fun x : ℝ ↦ Complex.exp (c * (x : ℂ)) * ψ x) :=
    HasCompactSupport.mul_left hψc
  refine ⟨hcs.toSchwartzMap hsm, fun x ↦ rfl, fun k n ↦ ?_⟩
  have hc : ‖c‖ = |t| := by simp [c]
  have hen (i : ℕ) (x : ℝ) :
      ‖iteratedFDeriv ℝ i (fun x : ℝ ↦ Complex.exp (c * (x : ℂ))) x‖ = |t| ^ i := by
    have hre : (c * (x : ℂ)).re = 0 := by simp [c]
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, referee_iteratedDeriv_cexp_apply, norm_mul,
      norm_pow, Complex.norm_exp, hc, hre, Real.exp_zero, mul_one]
  have hone : (0 : ℝ) ≤ 1 + |t| := by linarith [abs_nonneg t]
  have hRHS : 0 ≤ (1 + |t|) ^ n *
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * SchwartzMap.seminorm ℂ k (n - i) ψ :=
    mul_nonneg (pow_nonneg hone n)
      (Finset.sum_nonneg fun i _ ↦ mul_nonneg (Nat.cast_nonneg _) (apply_nonneg _ _))
  refine SchwartzMap.seminorm_le_bound ℂ k n _ hRHS fun x ↦ ?_
  change ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x : ℝ ↦ Complex.exp (c * (x : ℂ)) * ψ x) x‖ ≤ _
  have hleib := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) he (ψ.smooth ⊤) x (n := n)
    (by exact_mod_cast le_top)
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x : ℝ ↦ Complex.exp (c * (x : ℂ)) * ψ x) x‖
      ≤ ‖x‖ ^ k * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (fun x : ℝ ↦ Complex.exp (c * (x : ℂ))) x‖ *
          ‖iteratedFDeriv ℝ (n - i) ψ x‖ :=
        mul_le_mul_of_nonneg_left hleib (pow_nonneg (norm_nonneg x) k)
    _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * |t| ^ i *
          (‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) ψ x‖) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [hen]
        ring
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (1 + |t|) ^ n *
          SchwartzMap.seminorm ℂ k (n - i) ψ := by
        refine Finset.sum_le_sum fun i hi ↦ ?_
        have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have h1 : |t| ^ i ≤ (1 + |t|) ^ n :=
          (pow_le_pow_left₀ (abs_nonneg t) (by linarith [abs_nonneg t]) i).trans
            (pow_le_pow_right₀ (by linarith [abs_nonneg t]) hi')
        have h2 := SchwartzMap.le_seminorm ℂ k (n - i) ψ x
        exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)) h2
          (mul_nonneg (pow_nonneg (norm_nonneg x) k) (norm_nonneg _))
          (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hone n))
    _ = (1 + |t|) ^ n * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          SchwartzMap.seminorm ℂ k (n - i) ψ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        ring

#print axioms referee_modulated_profile

omit a in
/-- The integrand of the Mellin value of a radial test on the line `Re = 0`. -/
theorem referee_radial_integrand (η : PontryaginDual C𝔽) (θ : ℝ → ℝ)
    (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (hθc : HasCompactSupport θ) (f : 𝓢(ℝ, ℂ)) (t : ℝ) (g : C𝔽) :
    (refereeRadialTest (F := F) η θ hθ hθc f).val g *
        ideleClassNormTwist (F := F) η (shift(0, t)) g =
      (θ (logIdeleClassNorm F g) : ℂ) * (f (logIdeleClassNorm F g) *
        Complex.exp ((t : ℂ) * Complex.I * (logIdeleClassNorm F g : ℂ))) := by
  have hl : (positiveRealLogEquiv (m𝔽 g)).toAdd = logIdeleClassNorm F g :=
    positiveRealLogEquiv_apply _
  have htw : ideleClassNormTwist (F := F) η (shift(0, t)) g =
      (η g : ℂ) * Complex.exp (shift(0, t) * (logIdeleClassNorm F g : ℂ)) := by
    have h := stripProfile_jet (F := F) η 0 t 0 g
    unfold spectralZeroJet at h
    rw [pow_zero, mul_one, mul_one] at h
    exact h
  have hinv : (η⁻¹ g : Circle) = (η g)⁻¹ := rfl
  have hη : ((η⁻¹ g : Circle) : ℂ) * (η g : ℂ) = 1 := by
    rw [hinv, Circle.coe_inv, inv_mul_cancel₀ (Circle.coe_ne_zero _)]
  rw [refereeRadialTest_val, hl, htw, Complex.ofReal_zero, zero_add]
  linear_combination ((θ (logIdeleClassNorm F g) : ℂ) * (f (logIdeleClassNorm F g) *
    Complex.exp ((t : ℂ) * Complex.I * (logIdeleClassNorm F g : ℂ)))) * hη

omit a in
/-- The Mellin value of a radial test with profile `e^{-itx} ψ(x)` at the twist `i t` equals
the Mellin value of the radial test with profile `ψ` at the twist `0`. -/
theorem referee_radial_mellin_modulated (η : PontryaginDual C𝔽) (θ : ℝ → ℝ)
    (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (hθc : HasCompactSupport θ) (ψ f : 𝓢(ℝ, ℂ)) (t : ℝ)
    (hf : ∀ x : ℝ, f x = Complex.exp (-(t * Complex.I) * (x : ℂ)) * ψ x) :
    M(refereeRadialTest (F := F) η θ hθ hθc f, η, shift(0, t)) =
      M(refereeRadialTest (F := F) η θ hθ hθc ψ, η, shift(0, 0)) := by
  rw [(spectralConvolution_mellin_integrable _ η _).2,
    (spectralConvolution_mellin_integrable _ η _).2]
  refine integral_congr_ae (.of_forall fun g ↦ ?_)
  change (refereeRadialTest (F := F) η θ hθ hθc f).val g *
      ideleClassNormTwist (F := F) η (shift(0, t)) g =
    (refereeRadialTest (F := F) η θ hθ hθc ψ).val g *
      ideleClassNormTwist (F := F) η (shift(0, 0)) g
  rw [referee_radial_integrand, referee_radial_integrand, hf]
  have h1 : Complex.exp (-((t : ℂ) * Complex.I) * (logIdeleClassNorm F g : ℂ)) *
      Complex.exp ((t : ℂ) * Complex.I * (logIdeleClassNorm F g : ℂ)) = 1 := by
    rw [← Complex.exp_add]
    convert Complex.exp_zero using 2
    ring
  have h2 : Complex.exp (((0 : ℝ) : ℂ) * Complex.I * (logIdeleClassNorm F g : ℂ)) = 1 := by
    rw [Complex.ofReal_zero, zero_mul, zero_mul, Complex.exp_zero]
  rw [h2, mul_one]
  linear_combination ((θ (logIdeleClassNorm F g) : ℂ) * ψ (logIdeleClassNorm F g)) * h1

#print axioms referee_radial_mellin_modulated

/-- Width zero: a polynomial lower bound for the gaps between zeros of one row. Suppose the
conclusion of the strip residue lemma holds for every test (strip width zero, Sobolev exponent
above 3). Fix a row `ω`, a smooth compactly supported cutoff `θ` and a compactly supported
Schwartz profile `ψ`, and let `c₁` be the Mellin value at the twist `0` of the radial test
`x ↦ conj(χ_ω x) θ(log|x|) ψ(log|x|)`, that is, the integral of `θ(log|x|) ψ(log|x|)` over the
idele class group. Then there are `C` and `N` such that any two distinct zeros `(ω, 0, t)`,
`(ω, 0, t')` of that row with surviving zeroth jets satisfy
`|c₁| ≤ C (1 + |t|)^N |t − t'|`. -/
theorem referee_strip_zero_width_polynomial_gap (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    {α s : ℝ} (hα : 0 ≤ α) (hα0 : α = 0) (hs : 1 < s) (hs3 : 3 < s)
    (x : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s → Q(a, hStrip(hα), hs₀(hs)))
    (Λ : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s → StrongDual ℂ Q(a, hStrip(hα), hs₀(hs)))
    (hb : IsSpectralMarkushevichBasis x Λ)
    (hj : ∀ j, spectralSobolevDualEmbedding F a hStrip(hα) hs₀(hs) (Λ j) =
      (spectralStripJet_memLp (F := F) (fun ω ↦ χ ω) hα hs₀(hs) j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2))
    (θ : ℝ → ℝ) (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (hθc : HasCompactSupport θ)
    (ψ : 𝓢(ℝ, ℂ)) (hψc : HasCompactSupport ψ) (ω : PontryaginDual C₁)
    (h : ∀ φ : BruhatCompactSupport C𝔽,
      let H := Q(a, hStrip(hα), hs₀(hs))
      let A := spectralConvolution (F := F) a hStrip(hα) hs₀(hs) φ
      let jet (z : Zs(χ, α)) (m : Fin (Ns(χ, α, s, z))) :
          SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s :=
        ⟨(z.val.1, z.val.2.1, z.val.2.2, m.val), m.isLt⟩
      ∀ U : compactOperator (RingHom.id ℂ) H H,
        Summable (fun z : Zs(χ, α) ↦ ∑ m, Λ (jet z m) (A (U.val (x (jet z m)))))) :
    ∃ (C : ℝ) (N : ℕ), ∀ z z' : Zs(χ, α),
      0 < Ns(χ, α, s, z) → 0 < Ns(χ, α, s, z') → z.val.1 = ω → z'.val.1 = ω → z' ≠ z →
      ‖M(refereeRadialTest (F := F) (χ ω) θ hθ hθc ψ, χ ω, shift(0, 0))‖ ≤
        C * (1 + |z.val.2.2|) ^ N * |z.val.2.2 - z'.val.2.2| := by
  obtain ⟨S, C, hC0, hC⟩ :=
    referee_strip_zero_width_uniform a χ hα hα0 hs hs3 x Λ hb hj θ hθ hθc ω h
  let b (m : ℕ × ℕ) : ℝ := ∑ i ∈ Finset.range (m.2 + 1),
    (m.2.choose i : ℝ) * SchwartzMap.seminorm ℂ m.1 (m.2 - i) ψ
  have hb0 : ∀ m ∈ S, 0 ≤ b m := fun m _ ↦
    Finset.sum_nonneg fun i _ ↦ mul_nonneg (Nat.cast_nonneg _) (apply_nonneg _ _)
  let B : ℝ := ∑ m ∈ S, b m
  let N : ℕ := S.sup Prod.snd
  refine ⟨C * B, N, fun z z' hz hz' hzω hz'ω hne ↦ ?_⟩
  obtain ⟨f, hf, hfs⟩ := referee_modulated_profile ψ hψc z.val.2.2
  have hmain := hC f z z' hz hz' hzω hz'ω hne
  rw [referee_radial_mellin_modulated (F := F) (χ ω) θ hθ hθc ψ f z.val.2.2 hf] at hmain
  have hone : (1 : ℝ) ≤ 1 + |z.val.2.2| := by linarith [abs_nonneg z.val.2.2]
  have hpowN : 0 ≤ (1 + |z.val.2.2|) ^ N := pow_nonneg (by linarith) N
  have hsup : (S.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f ≤ (1 + |z.val.2.2|) ^ N * B := by
    refine Seminorm.finset_sup_apply_le (mul_nonneg hpowN (Finset.sum_nonneg hb0))
      fun m hm ↦ ?_
    have h1 : schwartzSeminormFamily ℂ ℝ ℂ m f ≤ (1 + |z.val.2.2|) ^ m.2 * b m := hfs m.1 m.2
    have h2 : (1 + |z.val.2.2|) ^ m.2 ≤ (1 + |z.val.2.2|) ^ N :=
      pow_le_pow_right₀ hone (Finset.le_sup (f := Prod.snd) hm)
    have h3 : b m ≤ B := Finset.single_le_sum hb0 hm
    exact h1.trans (mul_le_mul h2 h3 (hb0 m hm) hpowN)
  calc ‖M(refereeRadialTest (F := F) (χ ω) θ hθ hθc ψ, χ ω, shift(0, 0))‖
      ≤ C * (S.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f * |z.val.2.2 - z'.val.2.2| := hmain
    _ ≤ C * ((1 + |z.val.2.2|) ^ N * B) * |z.val.2.2 - z'.val.2.2| :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsup hC0) (abs_nonneg _)
    _ = C * B * (1 + |z.val.2.2|) ^ N * |z.val.2.2 - z'.val.2.2| := by ring

#print axioms referee_strip_zero_width_polynomial_gap

omit a in
/-- For a real cutoff `θ` with `θ 0 ≠ 0` and the profile `ψ = θ`, the Mellin value at the
twist `0` of the radial test is the integral of `θ(log|x|)^2` over the idele class group, a
positive number. -/
theorem referee_radial_mellin_ne_zero (η : PontryaginDual C𝔽) (θ : ℝ → ℝ)
    (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (hθc : HasCompactSupport θ) (hθ0 : θ 0 ≠ 0)
    (ψ : 𝓢(ℝ, ℂ)) (hψ : ∀ x, ψ x = (θ x : ℂ)) :
    M(refereeRadialTest (F := F) η θ hθ hθc ψ, η, shift(0, 0)) ≠ 0 := by
  have hI := (spectralConvolution_mellin_integrable
    (refereeRadialTest (F := F) η θ hθ hθc ψ) η (shift(0, 0))).1
  rw [(spectralConvolution_mellin_integrable _ η _).2]
  have hEq : (fun g ↦ (refereeRadialTest (F := F) η θ hθ hθc ψ).val g *
      ideleClassNormTwist (F := F) η (shift(0, 0)) g) =
      fun g ↦ (((θ (logIdeleClassNorm F g)) ^ 2 : ℝ) : ℂ) := by
    funext g
    rw [referee_radial_integrand, hψ, Complex.ofReal_zero, zero_mul, zero_mul, Complex.exp_zero,
      mul_one]
    push_cast
    ring
  rw [hEq] at hI
  have hint : ∫ g, (refereeRadialTest (F := F) η θ hθ hθc ψ).val g *
      ideleClassNormTwist (F := F) η (shift(0, 0)) g ∂μ𝔽 =
      ∫ g, (((θ (logIdeleClassNorm F g)) ^ 2 : ℝ) : ℂ) ∂μ𝔽 := congrArg (fun u ↦ ∫ g, u g ∂μ𝔽) hEq
  rw [hint, integral_complex_ofReal]
  have hIr : Integrable (fun g : C𝔽 ↦ (θ (logIdeleClassNorm F g)) ^ 2) μ𝔽 :=
    hI.re.congr (.of_forall fun g ↦ Complex.ofReal_re _)
  have hlog : Continuous (fun g : C𝔽 ↦ logIdeleClassNorm F g) :=
    Real.continuousOn_log.comp_continuous
      (NNReal.continuous_coe.comp (Units.continuous_val.comp
        (isProperMap_ideleClassNorm F).continuous))
      (fun g ↦ NNReal.coe_ne_zero.2 (ideleClassNorm F g).ne_zero)
  have hcont : Continuous (fun g : C𝔽 ↦ (θ (logIdeleClassNorm F g)) ^ 2) :=
    (hθ.continuous.comp hlog).pow 2
  have hpos : 0 < ∫ g, (θ (logIdeleClassNorm F g)) ^ 2 ∂μ𝔽 := by
    rw [integral_pos_iff_support_of_nonneg (fun g ↦ sq_nonneg _) hIr]
    refine hcont.isOpen_support.measure_pos μ𝔽 ⟨1, ?_⟩
    change (θ (logIdeleClassNorm F 1)) ^ 2 ≠ 0
    have h1 : logIdeleClassNorm F (1 : C𝔽) = 0 := by
      change Real.log ((ideleClassNorm F 1).val : ℝ) = 0
      rw [map_one, Units.val_one, NNReal.coe_one, Real.log_one]
    rw [h1]
    exact pow_ne_zero 2 hθ0
  exact_mod_cast hpos.ne'

#print axioms referee_radial_mellin_ne_zero

/-- Width zero, final form. Suppose the conclusion of the strip residue lemma holds for every
test (strip width zero, Sobolev exponent above 3). Then for every row `ω` there are `C` and `N`
such that any two distinct zeros `(ω, 0, t)`, `(ω, 0, t')` of that row with surviving zeroth
jets satisfy `1 ≤ C (1 + |t|)^N |t − t'|`. -/
theorem referee_strip_zero_width_gap (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    {α s : ℝ} (hα : 0 ≤ α) (hα0 : α = 0) (hs : 1 < s) (hs3 : 3 < s)
    (x : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s → Q(a, hStrip(hα), hs₀(hs)))
    (Λ : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s → StrongDual ℂ Q(a, hStrip(hα), hs₀(hs)))
    (hb : IsSpectralMarkushevichBasis x Λ)
    (hj : ∀ j, spectralSobolevDualEmbedding F a hStrip(hα) hs₀(hs) (Λ j) =
      (spectralStripJet_memLp (F := F) (fun ω ↦ χ ω) hα hs₀(hs) j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2))
    (ω : PontryaginDual C₁)
    (h : ∀ φ : BruhatCompactSupport C𝔽,
      let H := Q(a, hStrip(hα), hs₀(hs))
      let A := spectralConvolution (F := F) a hStrip(hα) hs₀(hs) φ
      let jet (z : Zs(χ, α)) (m : Fin (Ns(χ, α, s, z))) :
          SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s :=
        ⟨(z.val.1, z.val.2.1, z.val.2.2, m.val), m.isLt⟩
      ∀ U : compactOperator (RingHom.id ℂ) H H,
        Summable (fun z : Zs(χ, α) ↦ ∑ m, Λ (jet z m) (A (U.val (x (jet z m)))))) :
    ∃ (C : ℝ) (N : ℕ), ∀ z z' : Zs(χ, α),
      0 < Ns(χ, α, s, z) → 0 < Ns(χ, α, s, z') → z.val.1 = ω → z'.val.1 = ω → z' ≠ z →
      1 ≤ C * (1 + |z.val.2.2|) ^ N * |z.val.2.2 - z'.val.2.2| := by
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  have hθ : ContDiff ℝ (⊤ : ℕ∞) (b : ℝ → ℝ) := b.contDiff
  have hθc : HasCompactSupport (b : ℝ → ℝ) := b.hasCompactSupport
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ ↦ ((b y : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hθ
  have hcs : HasCompactSupport (fun y : ℝ ↦ ((b y : ℝ) : ℂ)) :=
    hθc.comp_left Complex.ofReal_zero
  let ψ : 𝓢(ℝ, ℂ) := hcs.toSchwartzMap hsm
  have hψc : HasCompactSupport ψ := hcs
  have hθ0 : b 0 ≠ 0 := (b.pos_of_mem_ball (Metric.mem_ball_self b.rOut_pos)).ne'
  have hne := referee_radial_mellin_ne_zero (F := F) (χ ω) b hθ hθc hθ0 ψ (fun _ ↦ rfl)
  obtain ⟨C, N, hC⟩ := referee_strip_zero_width_polynomial_gap a χ hα hα0 hs hs3 x Λ hb hj
    b hθ hθc ψ hψc ω h
  have hpos := norm_pos_iff.mpr hne
  refine ⟨C / ‖M(refereeRadialTest (F := F) (χ ω) b hθ hθc ψ, χ ω, shift(0, 0))‖, N,
    fun z z' hz hz' hzω hz'ω hne' ↦ ?_⟩
  have hmain := hC z z' hz hz' hzω hz'ω hne'
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hpos, one_mul]
  exact hmain

#print axioms referee_strip_zero_width_gap

/-- The library's strip residue lemma, applied at width zero to all tests, gives the
polynomial lower bound for the gaps. This term typechecks. It inherits the `sorry` of that
lemma. -/
theorem referee_strip_zero_width_gap_from_library (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω))
    {α s : ℝ} (hα : 0 ≤ α) (hα0 : α = 0) (hs : 1 < s) (hs3 : 3 < s)
    (x : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s → Q(a, hStrip(hα), hs₀(hs)))
    (Λ : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s → StrongDual ℂ Q(a, hStrip(hα), hs₀(hs)))
    (_hb : IsSpectralMarkushevichBasis x Λ)
    (_hj : ∀ j, spectralSobolevDualEmbedding F a hStrip(hα) hs₀(hs) (Λ j) =
      (spectralStripJet_memLp (F := F) (fun ω ↦ χ ω) hα hs₀(hs) j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2))
    (ω : PontryaginDual C₁) :
    ∃ (C : ℝ) (N : ℕ), ∀ z z' : Zs(χ, α),
      0 < Ns(χ, α, s, z) → 0 < Ns(χ, α, s, z') → z.val.1 = ω → z'.val.1 = ω → z' ≠ z →
      1 ≤ C * (1 + |z.val.2.2|) ^ N * |z.val.2.2 - z'.val.2.2| :=
  referee_strip_zero_width_gap a χ hα hα0 hs hs3 x Λ _hb _hj ω
    (fun φ ↦ spectralStripConvolution_traceCauchy_compact_block_series a χ _hχ hα hs φ x Λ _hb _hj)

#print axioms referee_strip_zero_width_gap_from_library

/-- The same, with the basis supplied by the library (`spectralStripMarkushevichBasis`) and the
strip residue lemma entering only as the proposition it asserts at width zero. If that
proposition holds for the centre `a`, the lifts `χ` and one Sobolev exponent `s > 3`, then in
every row the ordinates of distinct zeros on the line `Re = a` are polynomially separated. -/
theorem referee_strip_zero_width_gap_of_statement
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω)) {s : ℝ} (hs : 1 < s) (hs3 : 3 < s)
    (ω : PontryaginDual C₁)
    (hlemma : ∀ (φ : BruhatCompactSupport C𝔽)
      (x : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a 0 s → Q(a, hStrip(h₀), hs₀(hs)))
      (Λ : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a 0 s →
        StrongDual ℂ Q(a, hStrip(h₀), hs₀(hs))),
      IsSpectralMarkushevichBasis x Λ →
      (∀ j, spectralSobolevDualEmbedding F a hStrip(h₀) hs₀(hs) (Λ j) =
        (spectralStripJet_memLp (F := F) (fun ω ↦ χ ω) h₀ hs₀(hs) j).toLp
          (spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2)) →
      let H := Q(a, hStrip(h₀), hs₀(hs))
      let A := spectralConvolution (F := F) a hStrip(h₀) hs₀(hs) φ
      let jet (z : Zs(χ, (0 : ℝ))) (m : Fin (Ns(χ, (0 : ℝ), s, z))) :
          SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a 0 s :=
        ⟨(z.val.1, z.val.2.1, z.val.2.2, m.val), m.isLt⟩
      ∀ U : compactOperator (RingHom.id ℂ) H H,
        Summable (fun z : Zs(χ, (0 : ℝ)) ↦ ∑ m, Λ (jet z m) (A (U.val (x (jet z m)))))) :
    ∃ (C : ℝ) (N : ℕ), ∀ z z' : Zs(χ, (0 : ℝ)),
      0 < Ns(χ, (0 : ℝ), s, z) → 0 < Ns(χ, (0 : ℝ), s, z') → z.val.1 = ω → z'.val.1 = ω →
      z' ≠ z → 1 ≤ C * (1 + |z.val.2.2|) ^ N * |z.val.2.2 - z'.val.2.2| := by
  obtain ⟨-, x, Λ, hb, hj⟩ :=
    spectralStripMarkushevichBasis (F := F) (a := a) χ hχ h₀ hs₀(hs)
  exact referee_strip_zero_width_gap a χ h₀ rfl hs hs3 x Λ hb hj ω
    (fun φ ↦ hlemma φ x Λ hb hj)

#print axioms referee_strip_zero_width_gap_of_statement

/-- The hypothesis `hlemma` of `referee_strip_zero_width_gap_of_statement` is literally the
library's strip residue lemma at width zero: this term typechecks. It inherits the `sorry` of
that lemma. -/
theorem referee_strip_zero_width_gap_check (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω)) {s : ℝ} (hs : 1 < s) (hs3 : 3 < s)
    (ω : PontryaginDual C₁) :
    ∃ (C : ℝ) (N : ℕ), ∀ z z' : Zs(χ, (0 : ℝ)),
      0 < Ns(χ, (0 : ℝ), s, z) → 0 < Ns(χ, (0 : ℝ), s, z') → z.val.1 = ω → z'.val.1 = ω →
      z' ≠ z → 1 ≤ C * (1 + |z.val.2.2|) ^ N * |z.val.2.2 - z'.val.2.2| :=
  referee_strip_zero_width_gap_of_statement a χ hχ hs hs3 ω
    (fun φ x Λ hb hj ↦
      spectralStripConvolution_traceCauchy_compact_block_series a χ hχ h₀ hs φ x Λ hb hj)

#print axioms referee_strip_zero_width_gap_check

end Uniform

/-! ## Part H: the line residue lemma for all tests (isolated zeros of one row) -/

section LineUniform

open scoped SchwartzMap

variable (a : ℝ)

local notation "Zl(" χ ")" => {z : PontryaginDual C₁ × ℝ // 0 < order(χ z.1, shift(a, z.2))}
local notation "Nl(" χ ", " s ", " z ")" => spectralBoundaryMultiplicity s (mult(χ (z).val.1,
  shift(a, (z).val.2)))

open Classical in
/-- Line, all radial tests of one row at once. Suppose the conclusion of the line residue lemma
holds for every test and every numbering with the prescribed rows (Sobolev exponent above 3).
Fix a row `ω` and a cutoff `θ`. Then there are finitely many Schwartz seminorms and a constant
`C` such that for every Schwartz profile `f`, every zero `(ω, t)` of that row which is isolated
among the zeros of the row, and every other zero `(ω, t')` of the row, the Mellin value at
`i t` of the radial test with profile `f` is at most `C · (sup of the seminorms)(f) · |t − t'|`. -/
theorem referee_line_uniform (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    {s : ℝ} (hs : 1 < s) (hs3 : 3 < s)
    (eχ : PontryaginDual C₁ ↪ ℕ) (e₀ : Zl(χ) ↪ ℕ × ℕ)
    (Λ : SpectralLineJetIndex (F := F) χ a s → StrongDual ℂ Q(a, h₀, hs₀(hs)))
    (hj : ∀ j, spectralSobolevDualEmbedding F a h₀ hs₀(hs) (Λ j) =
      (spectralLineJet_memLp (F := F) χ hs j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) 0 j.val.2.1 j.val.2.2))
    (θ : ℝ → ℝ) (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (hθc : HasCompactSupport θ)
    (ω : PontryaginDual C₁)
    (h : ∀ φ : BruhatCompactSupport C𝔽, ∀ e : Zl(χ) ↪ ℕ × ℕ, (∀ z, (e z).1 = eχ z.val.1) →
      let box (ij : ℕ × ℕ) :=
        ((Finset.Iic ij.1).product (Finset.Iic ij.2)).preimage e e.injective.injOn
      let jet (z : Zl(χ)) (m : Fin (Nl(χ, s, z))) : SpectralLineJetIndex (F := F) χ a s :=
        ⟨(z.val.1, z.val.2, m.val), m.isLt⟩
      let A := spectralConvolution (F := F) a h₀ hs₀(hs) φ
      ∀ ε > (0 : ℝ), ∃ i, ∀ j ≥ i, ∀ (K : Finset (SpectralLineJetIndex (F := F) χ a s))
        (v : SpectralLineJetIndex (F := F) χ a s → Q(a, h₀, hs₀(hs))),
        (∀ k ∉ K, v k = 0) → ‖∑ k ∈ K, (Λ k).smulRight (v k)‖ ≤ 1 →
        (∑ z ∈ box j \ box i, ∑ m : Fin (Nl(χ, s, z)), Λ (jet z m) (A (v (jet z m)))).re ≤ ε) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ (f : 𝓢(ℝ, ℂ)) (z z' : Zl(χ)) (δ : ℝ),
      0 < Nl(χ, s, z) → 0 < Nl(χ, s, z') → z.val.1 = ω → z'.val.1 = ω → z' ≠ z → 0 < δ →
      (∀ u : Zl(χ), 0 < Nl(χ, s, u) → u.val.1 = ω → u ≠ z → δ ≤ |z.val.2 - u.val.2|) →
      ‖M(refereeRadialTest (F := F) (χ ω) θ hθ hθc f, χ ω, shift(0, z.val.2))‖ ≤
        C * (S.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f * |z.val.2 - z'.val.2| := by
  have hcomplete : CompleteSpace 𝓢(ℝ, ℂ) := completeSpace_schwartzMap
  have hcount : (uniformity 𝓢(ℝ, ℂ)).IsCountablyGenerated := by
    rw [uniformity_eq_comap_nhds_zero 𝓢(ℝ, ℂ)]
    infer_instance
  have hbaire : BaireSpace 𝓢(ℝ, ℂ) := BaireSpace.of_completelyPseudoMetrizable
  choose E hE using fun t : ℝ ↦
    referee_radial_mellin_clm (F := F) (χ ω) θ hθ hθc (shift(0, t))
  let V (z : Zl(χ)) := {u : Zl(χ) // 0 < Nl(χ, s, u) ∧ u.val.1 = ω ∧ u ≠ z}
  let G (z : Zl(χ)) : ℝ := ⨅ u : V z, |z.val.2 - u.val.val.2|
  have hG0 (z : Zl(χ)) : 0 ≤ G z := Real.iInf_nonneg fun _ ↦ abs_nonneg _
  have hGle (z : Zl(χ)) (u : V z) : G z ≤ |z.val.2 - u.val.val.2| :=
    ciInf_le ⟨0, by rintro _ ⟨w, rfl⟩; exact abs_nonneg _⟩ u
  let ι := {p : Zl(χ) × Zl(χ) × ℝ // 0 < Nl(χ, s, p.1) ∧ 0 < Nl(χ, s, p.2.1) ∧
    p.1.val.1 = ω ∧ p.2.1.val.1 = ω ∧ p.2.1 ≠ p.1 ∧ 0 < p.2.2 ∧
    ∀ u : Zl(χ), 0 < Nl(χ, s, u) → u.val.1 = ω → u ≠ p.1 → p.2.2 ≤ |p.1.val.2 - u.val.2|}
  let d (i : ι) : ℝ := |i.val.1.val.2 - i.val.2.1.val.2|
  let p (i : ι) : Seminorm ℂ 𝓢(ℝ, ℂ) :=
    (normSeminorm ℂ ℂ).comp ((((d i)⁻¹ : ℝ) : ℂ) • E i.val.1.val.2).toLinearMap
  have hp_apply (i : ι) (f : 𝓢(ℝ, ℂ)) : p i f = (d i)⁻¹ * ‖E i.val.1.val.2 f‖ := by
    change ‖(((d i)⁻¹ : ℝ) : ℂ) • E i.val.1.val.2 f‖ = _
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr (abs_nonneg _))]
  have hpc (i : ι) : Continuous (p i) := by
    change Continuous fun f ↦ ‖((((d i)⁻¹ : ℝ) : ℂ) • E i.val.1.val.2) f‖
    exact continuous_norm.comp (ContinuousLinearMap.continuous _)
  have hGpos (i : ι) : 0 < G i.val.1 := by
    have hne : Nonempty (V i.val.1) :=
      ⟨⟨i.val.2.1, i.property.2.1, i.property.2.2.2.1, i.property.2.2.2.2.1⟩⟩
    exact lt_of_lt_of_le i.property.2.2.2.2.2.1
      (le_ciInf fun u ↦ i.property.2.2.2.2.2.2 u.val u.property.1 u.property.2.1 u.property.2.2)
  have hdG (i : ι) : G i.val.1 ≤ d i :=
    hGle i.val.1 ⟨i.val.2.1, i.property.2.1, i.property.2.2.2.1, i.property.2.2.2.2.1⟩
  have hbdd : BddAbove (range p) := by
    rw [Seminorm.bddAbove_range_iff]
    intro f
    obtain ⟨κ, hκ, hgap⟩ := referee_line_mellin_gap a χ hs hs3
      (refereeRadialTest (F := F) (χ ω) θ hθ hθc f) eχ e₀ Λ hj (h _)
    obtain ⟨S, hS⟩ := hgap 1 one_pos
    have hterm0 : ∀ u ∈ S, 0 ≤ (G u)⁻¹ * ‖E u.val.2 f‖ := fun u _ ↦
      mul_nonneg (inv_nonneg.mpr (hG0 u)) (norm_nonneg _)
    have hsum0 : 0 ≤ ∑ u ∈ S, (G u)⁻¹ * ‖E u.val.2 f‖ := Finset.sum_nonneg hterm0
    refine ⟨κ + ∑ u ∈ S, (G u)⁻¹ * ‖E u.val.2 f‖, ?_⟩
    rintro _ ⟨i, rfl⟩
    change p i f ≤ _
    rw [hp_apply]
    have hdpos : 0 < d i := lt_of_lt_of_le (hGpos i) (hdG i)
    by_cases hiS : i.val.1 ∈ S
    · have h1 : (d i)⁻¹ * ‖E i.val.1.val.2 f‖ ≤ (G i.val.1)⁻¹ * ‖E i.val.1.val.2 f‖ :=
        mul_le_mul_of_nonneg_right (inv_anti₀ (hGpos i) (hdG i)) (norm_nonneg _)
      have h2 := Finset.single_le_sum hterm0 hiS
      linarith
    · have hbi := hS i.val.1 hiS i.property.1 i.val.2.1 i.property.2.1
        (i.property.2.2.2.1.trans i.property.2.2.1.symm) i.property.2.2.2.2.1
      rw [i.property.2.2.1] at hbi
      have hbi' : ‖E i.val.1.val.2 f‖ ≤ 1 * κ * d i := by
        rw [hE]
        exact hbi
      rw [inv_mul_le_iff₀ hdpos]
      calc ‖E i.val.1.val.2 f‖ ≤ 1 * κ * d i := hbi'
        _ = d i * κ := by ring
        _ ≤ d i * (κ + ∑ u ∈ S, (G u)⁻¹ * ‖E u.val.2 f‖) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hsum0) hdpos.le
  have hcont : Continuous ⇑(⨆ i, p i) := by
    rw [Seminorm.coe_iSup_eq hbdd]
    exact Seminorm.continuous_iSup p hpc hbdd
  obtain ⟨S, C, -, hC⟩ :=
    Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ ℝ ℂ) (⨆ i, p i) hcont
  refine ⟨S, C, C.coe_nonneg, fun f z z' δ hz hz' hzω hz'ω hne hδ hiso ↦ ?_⟩
  let i : ι := ⟨(z, z', δ), hz, hz', hzω, hz'ω, hne, hδ, hiso⟩
  have h1 : p i f ≤ (C • S.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f :=
    (Seminorm.le_def.mp (le_ciSup hbdd i) f).trans (Seminorm.le_def.mp hC f)
  rw [hp_apply] at h1
  have h2 : (C • S.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f =
      (C : ℝ) * (S.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f := rfl
  rw [h2] at h1
  rw [← hE]
  have hdpos : 0 < d i := lt_of_lt_of_le (hGpos i) (hdG i)
  have hdi : d i = |z.val.2 - z'.val.2| := rfl
  rw [inv_mul_le_iff₀ hdpos] at h1
  rw [← hdi, mul_comm]
  exact h1

#print axioms referee_line_uniform

open Classical in
/-- Line, final form. Suppose the conclusion of the line residue lemma holds for every test and
every numbering with the prescribed rows (Sobolev exponent above 3). Then for every row `ω`
there are `C` and `N` such that every zero `(ω, t)` of the row which is isolated among the zeros
of the row, and every other zero `(ω, t')` of the row, satisfy `1 ≤ C (1 + |t|)^N |t − t'|`. -/
theorem referee_line_gap (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    {s : ℝ} (hs : 1 < s) (hs3 : 3 < s)
    (eχ : PontryaginDual C₁ ↪ ℕ) (e₀ : Zl(χ) ↪ ℕ × ℕ)
    (Λ : SpectralLineJetIndex (F := F) χ a s → StrongDual ℂ Q(a, h₀, hs₀(hs)))
    (hj : ∀ j, spectralSobolevDualEmbedding F a h₀ hs₀(hs) (Λ j) =
      (spectralLineJet_memLp (F := F) χ hs j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) 0 j.val.2.1 j.val.2.2))
    (ω : PontryaginDual C₁)
    (h : ∀ φ : BruhatCompactSupport C𝔽, ∀ e : Zl(χ) ↪ ℕ × ℕ, (∀ z, (e z).1 = eχ z.val.1) →
      let box (ij : ℕ × ℕ) :=
        ((Finset.Iic ij.1).product (Finset.Iic ij.2)).preimage e e.injective.injOn
      let jet (z : Zl(χ)) (m : Fin (Nl(χ, s, z))) : SpectralLineJetIndex (F := F) χ a s :=
        ⟨(z.val.1, z.val.2, m.val), m.isLt⟩
      let A := spectralConvolution (F := F) a h₀ hs₀(hs) φ
      ∀ ε > (0 : ℝ), ∃ i, ∀ j ≥ i, ∀ (K : Finset (SpectralLineJetIndex (F := F) χ a s))
        (v : SpectralLineJetIndex (F := F) χ a s → Q(a, h₀, hs₀(hs))),
        (∀ k ∉ K, v k = 0) → ‖∑ k ∈ K, (Λ k).smulRight (v k)‖ ≤ 1 →
        (∑ z ∈ box j \ box i, ∑ m : Fin (Nl(χ, s, z)), Λ (jet z m) (A (v (jet z m)))).re ≤ ε) :
    ∃ (C : ℝ) (N : ℕ), ∀ (z z' : Zl(χ)) (δ : ℝ),
      0 < Nl(χ, s, z) → 0 < Nl(χ, s, z') → z.val.1 = ω → z'.val.1 = ω → z' ≠ z → 0 < δ →
      (∀ u : Zl(χ), 0 < Nl(χ, s, u) → u.val.1 = ω → u ≠ z → δ ≤ |z.val.2 - u.val.2|) →
      1 ≤ C * (1 + |z.val.2|) ^ N * |z.val.2 - z'.val.2| := by
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  have hθ : ContDiff ℝ (⊤ : ℕ∞) (b : ℝ → ℝ) := b.contDiff
  have hθc : HasCompactSupport (b : ℝ → ℝ) := b.hasCompactSupport
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ ↦ ((b y : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hθ
  have hcs : HasCompactSupport (fun y : ℝ ↦ ((b y : ℝ) : ℂ)) :=
    hθc.comp_left Complex.ofReal_zero
  let ψ : 𝓢(ℝ, ℂ) := hcs.toSchwartzMap hsm
  have hψc : HasCompactSupport ψ := hcs
  have hθ0 : b 0 ≠ 0 := (b.pos_of_mem_ball (Metric.mem_ball_self b.rOut_pos)).ne'
  have hne := referee_radial_mellin_ne_zero (F := F) (χ ω) b hθ hθc hθ0 ψ (fun _ ↦ rfl)
  have hpos := norm_pos_iff.mpr hne
  obtain ⟨S, C, hC0, hC⟩ := referee_line_uniform a χ hs hs3 eχ e₀ Λ hj b hθ hθc ω h
  let bm (m : ℕ × ℕ) : ℝ := ∑ i ∈ Finset.range (m.2 + 1),
    (m.2.choose i : ℝ) * SchwartzMap.seminorm ℂ m.1 (m.2 - i) ψ
  have hb0 : ∀ m ∈ S, 0 ≤ bm m := fun m _ ↦
    Finset.sum_nonneg fun i _ ↦ mul_nonneg (Nat.cast_nonneg _) (apply_nonneg _ _)
  let B : ℝ := ∑ m ∈ S, bm m
  let N : ℕ := S.sup Prod.snd
  refine ⟨C * B / ‖M(refereeRadialTest (F := F) (χ ω) b hθ hθc ψ, χ ω, shift(0, 0))‖, N,
    fun z z' δ hz hz' hzω hz'ω hne' hδ hiso ↦ ?_⟩
  obtain ⟨f, hf, hfs⟩ := referee_modulated_profile ψ hψc z.val.2
  have hmain := hC f z z' δ hz hz' hzω hz'ω hne' hδ hiso
  rw [referee_radial_mellin_modulated (F := F) (χ ω) b hθ hθc ψ f z.val.2 hf] at hmain
  have hone : (1 : ℝ) ≤ 1 + |z.val.2| := by linarith [abs_nonneg z.val.2]
  have hpowN : 0 ≤ (1 + |z.val.2|) ^ N := pow_nonneg (by linarith) N
  have hsup : (S.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f ≤ (1 + |z.val.2|) ^ N * B := by
    refine Seminorm.finset_sup_apply_le (mul_nonneg hpowN (Finset.sum_nonneg hb0))
      fun m hm ↦ ?_
    have h1 : schwartzSeminormFamily ℂ ℝ ℂ m f ≤ (1 + |z.val.2|) ^ m.2 * bm m := hfs m.1 m.2
    have h2 : (1 + |z.val.2|) ^ m.2 ≤ (1 + |z.val.2|) ^ N :=
      pow_le_pow_right₀ hone (Finset.le_sup (f := Prod.snd) hm)
    have h3 : bm m ≤ B := Finset.single_le_sum hb0 hm
    exact h1.trans (mul_le_mul h2 h3 (hb0 m hm) hpowN)
  have hfinal : ‖M(refereeRadialTest (F := F) (χ ω) b hθ hθc ψ, χ ω, shift(0, 0))‖ ≤
      C * B * (1 + |z.val.2|) ^ N * |z.val.2 - z'.val.2| :=
    calc ‖M(refereeRadialTest (F := F) (χ ω) b hθ hθc ψ, χ ω, shift(0, 0))‖
        ≤ C * (S.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f * |z.val.2 - z'.val.2| := hmain
      _ ≤ C * ((1 + |z.val.2|) ^ N * B) * |z.val.2 - z'.val.2| :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsup hC0) (abs_nonneg _)
      _ = C * B * (1 + |z.val.2|) ^ N * |z.val.2 - z'.val.2| := by ring
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hpos, one_mul]
  exact hfinal

#print axioms referee_line_gap

open Classical in
/-- The library's line residue lemma, applied to all tests and numberings, gives the polynomial
lower bound for the gaps at isolated zeros. This term typechecks. It inherits the `sorry` of
that lemma. -/
theorem referee_line_gap_from_library (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice (F := F) χ)
    {s : ℝ} (hs : 1 < s) (hs3 : 3 < s)
    (eχ : PontryaginDual C₁ ↪ ℕ) (e₀ : Zl(χ) ↪ ℕ × ℕ)
    (Λ : SpectralLineJetIndex (F := F) χ a s → StrongDual ℂ Q(a, h₀, hs₀(hs)))
    (_hj : ∀ j, spectralSobolevDualEmbedding F a h₀ hs₀(hs) (Λ j) =
      (spectralLineJet_memLp (F := F) χ hs j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) 0 j.val.2.1 j.val.2.2))
    (ω : PontryaginDual C₁) :
    ∃ (C : ℝ) (N : ℕ), ∀ (z z' : Zl(χ)) (δ : ℝ),
      0 < Nl(χ, s, z) → 0 < Nl(χ, s, z') → z.val.1 = ω → z'.val.1 = ω → z' ≠ z → 0 < δ →
      (∀ u : Zl(χ), 0 < Nl(χ, s, u) → u.val.1 = ω → u ≠ z → δ ≤ |z.val.2 - u.val.2|) →
      1 ≤ C * (1 + |z.val.2|) ^ N * |z.val.2 - z'.val.2| :=
  referee_line_gap a χ hs hs3 eχ e₀ Λ _hj ω
    (fun φ e he ↦
      spectralLineConvolution_traceCauchy_scalar_shell (F := F) a χ _hχ hs φ eχ e he Λ _hj)

#print axioms referee_line_gap_from_library

/-! ### Zeros of one row are isolated, so the isolation hypothesis can be dropped -/

omit a in
/-- A point of finite positive meromorphic order has a punctured neighbourhood without points
of positive order. -/
theorem referee_order_pos_isolated (f : ℂ → ℂ) (x : ℂ) (hpos : 0 < meromorphicOrderAt f x)
    (htop : meromorphicOrderAt f x ≠ ⊤) :
    ∃ δ > (0 : ℝ), ∀ y : ℂ, y ≠ x → dist y x < δ → ¬ 0 < meromorphicOrderAt f y := by
  have hm : MeromorphicAt f x := meromorphicAt_of_meromorphicOrderAt_ne_zero hpos.ne'
  have h1 := (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hm).mp htop
  have h2 := hm.eventually_analyticAt
  have h3 : ∀ᶠ y in 𝓝[≠] x, ¬ 0 < meromorphicOrderAt f y := by
    filter_upwards [h1, h2] with y hy hay
    rw [hay.meromorphicOrderAt_eq, hay.analyticOrderAt_eq_zero.mpr hy]
    simp
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h3
  obtain ⟨δ, hδ, hball⟩ := h3
  exact ⟨δ, hδ, fun y hyx hd ↦ hball hd hyx⟩

/-- Every zero of a row with a surviving zeroth jet is isolated among the zeros of that row. -/
theorem referee_line_zero_isolated (χ : PontryaginDual C₁ → PontryaginDual C𝔽) {s : ℝ}
    (z : Zl(χ)) (hz : 0 < Nl(χ, s, z)) :
    ∃ δ > (0 : ℝ), ∀ u : Zl(χ), u.val.1 = z.val.1 → u ≠ z → δ ≤ |z.val.2 - u.val.2| := by
  have hpos := z.property
  have htop : order(χ z.val.1, shift(a, z.val.2)) ≠ ⊤ := by
    intro htop
    have hm : mult(χ z.val.1, shift(a, z.val.2)) = 0 := by
      rw [htop]
      simp
    unfold spectralBoundaryMultiplicity at hz
    rw [hm] at hz
    simp at hz
  obtain ⟨δ, hδ, hiso⟩ := referee_order_pos_isolated _ _ hpos htop
  refine ⟨δ, hδ, fun u hrow hne ↦ ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  have hne2 : u.val.2 ≠ z.val.2 := fun h2 ↦ hne (Subtype.ext (Prod.ext hrow h2))
  have hdiff : shift(a, u.val.2) - shift(a, z.val.2) =
      ((u.val.2 - z.val.2 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  have hy : shift(a, u.val.2) ≠ shift(a, z.val.2) := by
    intro hEq
    apply hne2
    have him := congrArg Complex.im hEq
    simpa using him
  have hd : dist (shift(a, u.val.2)) (shift(a, z.val.2)) < δ := by
    rw [Complex.dist_eq, hdiff, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_sub_comm]
    exact hlt
  have hu := u.property
  rw [hrow] at hu
  exact hiso _ hy hd hu

#print axioms referee_line_zero_isolated

open Classical in
/-- Line, final form without the isolation hypothesis. Suppose the conclusion of the line
residue lemma holds for every test and every numbering with the prescribed rows (Sobolev
exponent above 3). Then for every row `ω` there are `C` and `N` such that any two distinct zeros
`(ω, t)`, `(ω, t')` of that row with surviving zeroth jets satisfy
`1 ≤ C (1 + |t|)^N |t − t'|`. -/
theorem referee_line_gap_all (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    {s : ℝ} (hs : 1 < s) (hs3 : 3 < s)
    (eχ : PontryaginDual C₁ ↪ ℕ) (e₀ : Zl(χ) ↪ ℕ × ℕ)
    (Λ : SpectralLineJetIndex (F := F) χ a s → StrongDual ℂ Q(a, h₀, hs₀(hs)))
    (hj : ∀ j, spectralSobolevDualEmbedding F a h₀ hs₀(hs) (Λ j) =
      (spectralLineJet_memLp (F := F) χ hs j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) 0 j.val.2.1 j.val.2.2))
    (ω : PontryaginDual C₁)
    (h : ∀ φ : BruhatCompactSupport C𝔽, ∀ e : Zl(χ) ↪ ℕ × ℕ, (∀ z, (e z).1 = eχ z.val.1) →
      let box (ij : ℕ × ℕ) :=
        ((Finset.Iic ij.1).product (Finset.Iic ij.2)).preimage e e.injective.injOn
      let jet (z : Zl(χ)) (m : Fin (Nl(χ, s, z))) : SpectralLineJetIndex (F := F) χ a s :=
        ⟨(z.val.1, z.val.2, m.val), m.isLt⟩
      let A := spectralConvolution (F := F) a h₀ hs₀(hs) φ
      ∀ ε > (0 : ℝ), ∃ i, ∀ j ≥ i, ∀ (K : Finset (SpectralLineJetIndex (F := F) χ a s))
        (v : SpectralLineJetIndex (F := F) χ a s → Q(a, h₀, hs₀(hs))),
        (∀ k ∉ K, v k = 0) → ‖∑ k ∈ K, (Λ k).smulRight (v k)‖ ≤ 1 →
        (∑ z ∈ box j \ box i, ∑ m : Fin (Nl(χ, s, z)), Λ (jet z m) (A (v (jet z m)))).re ≤ ε) :
    ∃ (C : ℝ) (N : ℕ), ∀ z z' : Zl(χ),
      0 < Nl(χ, s, z) → 0 < Nl(χ, s, z') → z.val.1 = ω → z'.val.1 = ω → z' ≠ z →
      1 ≤ C * (1 + |z.val.2|) ^ N * |z.val.2 - z'.val.2| := by
  obtain ⟨C, N, hC⟩ := referee_line_gap a χ hs hs3 eχ e₀ Λ hj ω h
  refine ⟨C, N, fun z z' hz hz' hzω hz'ω hne ↦ ?_⟩
  obtain ⟨δ, hδ, hiso⟩ := referee_line_zero_isolated a χ z hz
  exact hC z z' δ hz hz' hzω hz'ω hne hδ
    (fun u _ huω hune ↦ hiso u (huω.trans hzω.symm) hune)

#print axioms referee_line_gap_all

open Classical in
/-- The library's line residue lemma, applied to all tests and numberings, gives the polynomial
lower bound for the gaps in every row. This term typechecks. It inherits the `sorry` of that
lemma. -/
theorem referee_line_gap_all_from_library (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice (F := F) χ)
    {s : ℝ} (hs : 1 < s) (hs3 : 3 < s)
    (eχ : PontryaginDual C₁ ↪ ℕ) (e₀ : Zl(χ) ↪ ℕ × ℕ)
    (Λ : SpectralLineJetIndex (F := F) χ a s → StrongDual ℂ Q(a, h₀, hs₀(hs)))
    (_hj : ∀ j, spectralSobolevDualEmbedding F a h₀ hs₀(hs) (Λ j) =
      (spectralLineJet_memLp (F := F) χ hs j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) 0 j.val.2.1 j.val.2.2))
    (ω : PontryaginDual C₁) :
    ∃ (C : ℝ) (N : ℕ), ∀ z z' : Zl(χ),
      0 < Nl(χ, s, z) → 0 < Nl(χ, s, z') → z.val.1 = ω → z'.val.1 = ω → z' ≠ z →
      1 ≤ C * (1 + |z.val.2|) ^ N * |z.val.2 - z'.val.2| :=
  referee_line_gap_all a χ hs hs3 eχ e₀ Λ _hj ω
    (fun φ e he ↦
      spectralLineConvolution_traceCauchy_scalar_shell (F := F) a χ _hχ hs φ eχ e he Λ _hj)

#print axioms referee_line_gap_all_from_library

open Classical in
/-- The same, with the functionals and the numberings supplied by the library
(`spectralLineMarkushevichBasis`, `spectralLineConvolution_nuclear_indices`) and the line
residue lemma entering only as the proposition it asserts. If that proposition holds for the
centre `a`, the lifts `χ` and one Sobolev exponent `s > 3`, then in every row the ordinates of
distinct zeros on the line `Re = a` are polynomially separated. -/
theorem referee_line_gap_of_statement (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice (F := F) χ) {s : ℝ} (hs : 1 < s) (hs3 : 3 < s)
    (ω : PontryaginDual C₁)
    (hlemma : ∀ (φ : BruhatCompactSupport C𝔽) (eχ : PontryaginDual C₁ ↪ ℕ)
      (e : Zl(χ) ↪ ℕ × ℕ), (∀ z, (e z).1 = eχ z.val.1) →
      ∀ (Λ : SpectralLineJetIndex (F := F) χ a s → StrongDual ℂ Q(a, h₀, hs₀(hs))),
      (∀ j, spectralSobolevDualEmbedding F a h₀ hs₀(hs) (Λ j) =
        (spectralLineJet_memLp (F := F) χ hs j).toLp
          (spectralZeroJet (F := F) (χ j.val.1) 0 j.val.2.1 j.val.2.2)) →
      let box (ij : ℕ × ℕ) :=
        ((Finset.Iic ij.1).product (Finset.Iic ij.2)).preimage e e.injective.injOn
      let jet (z : Zl(χ)) (m : Fin (Nl(χ, s, z))) : SpectralLineJetIndex (F := F) χ a s :=
        ⟨(z.val.1, z.val.2, m.val), m.isLt⟩
      let A := spectralConvolution (F := F) a h₀ hs₀(hs) φ
      ∀ ε > (0 : ℝ), ∃ i, ∀ j ≥ i, ∀ (K : Finset (SpectralLineJetIndex (F := F) χ a s))
        (v : SpectralLineJetIndex (F := F) χ a s → Q(a, h₀, hs₀(hs))),
        (∀ k ∉ K, v k = 0) → ‖∑ k ∈ K, (Λ k).smulRight (v k)‖ ≤ 1 →
        (∑ z ∈ box j \ box i, ∑ m : Fin (Nl(χ, s, z)), Λ (jet z m) (A (v (jet z m)))).re ≤ ε) :
    ∃ (C : ℝ) (N : ℕ), ∀ z z' : Zl(χ),
      0 < Nl(χ, s, z) → 0 < Nl(χ, s, z') → z.val.1 = ω → z'.val.1 = ω → z' ≠ z →
      1 ≤ C * (1 + |z.val.2|) ^ N * |z.val.2 - z'.val.2| := by
  obtain ⟨-, x, Λ, hb, hj⟩ := spectralLineMarkushevichBasis (F := F) (a := a) χ hχ hs
  obtain ⟨r, e, he⟩ := spectralLineConvolution_nuclear_indices χ
    (fun z : Zl(χ) ↦ z.val.1) (fun z ↦ shift(a, z.val.2)) (by
      intro i j h
      have hrow := congrArg Prod.fst h
      exact Subtype.ext (Prod.ext hrow
        (by simpa using congrArg (fun p ↦ (p.2 : ℂ).im) h))) (fun z ↦ z.property)
  exact referee_line_gap_all a χ hs hs3 r e Λ hj ω
    (fun φ e' he' ↦ hlemma φ r e' he' Λ hj)

#print axioms referee_line_gap_of_statement

open Classical in
/-- The hypothesis `hlemma` of `referee_line_gap_of_statement` is literally the library's line
residue lemma: this term typechecks. It inherits the `sorry` of that lemma. -/
theorem referee_line_gap_check (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice (F := F) χ) {s : ℝ} (hs : 1 < s) (hs3 : 3 < s)
    (ω : PontryaginDual C₁) :
    ∃ (C : ℝ) (N : ℕ), ∀ z z' : Zl(χ),
      0 < Nl(χ, s, z) → 0 < Nl(χ, s, z') → z.val.1 = ω → z'.val.1 = ω → z' ≠ z →
      1 ≤ C * (1 + |z.val.2|) ^ N * |z.val.2 - z'.val.2| :=
  referee_line_gap_of_statement a χ hχ hs hs3 ω
    (fun φ eχ e he Λ hj ↦
      spectralLineConvolution_traceCauchy_scalar_shell (F := F) a χ hχ hs φ eχ e he Λ hj)

#print axioms referee_line_gap_check

end LineUniform


/-! ## Verifier's additions (independent check; not part of the prover's file) -/

section VerifierStrip

variable (a : ℝ)

local notation "Zs(" χ ", " α ")" => {z : PontryaginDual C₁ × ℝ × ℝ //
  z.2.1 ∈ Icc (-α) α ∧ 0 < order(χ z.1, shift(a + z.2.1, z.2.2))}
local notation "Ns(" χ ", " α ", " s ", " z ")" => spectralStripMultiplicity α s (z).val.2.1
  (mult(χ (z).val.1, shift(a + (z).val.2.1, (z).val.2.2)))

/-- The by-hand claim of the report: at width zero and `s > 3` every zero of finite order has a
surviving zeroth jet. -/
theorem verifier_Ns_pos (χ : PontryaginDual C₁ → PontryaginDual C𝔽) {s : ℝ} (hs3 : 3 < s)
    (z : Zs(χ, (0 : ℝ)))
    (hfin : order(χ z.val.1, shift(a + z.val.2.1, z.val.2.2)) ≠ ⊤) :
    0 < Ns(χ, (0 : ℝ), s, z) := by
  have hb : z.val.2.1 = 0 := by
    have h₁ : -(0 : ℝ) ≤ z.val.2.1 := z.property.1.1
    have h₂ : z.val.2.1 ≤ 0 := z.property.1.2
    exact le_antisymm h₂ (by linarith)
  have key : ∀ o : WithTop ℤ, 0 < o → o ≠ ⊤ → 0 < o.untop₀.toNat := by
    intro o hpos hfin
    cases o with
    | top => exact absurd rfl hfin
    | coe n =>
      rw [WithTop.untop₀_coe]
      have hn : (0 : ℤ) < n := by exact_mod_cast hpos
      omega
  have hk : 0 < mult(χ z.val.1, shift(a + z.val.2.1, z.val.2.2)) := key _ z.property.2 hfin
  rw [spectralStripMultiplicity_boundary (le_refl (0 : ℝ)) (Or.inr hb)]
  unfold spectralBoundaryMultiplicity
  exact lt_min hk (Nat.ceil_pos.mpr (by linarith))

#print axioms verifier_Ns_pos

/-- The report's final implication, restated by the verifier. The hypothesis is taken with
`type_of%` from the library lemma itself at width zero (so it is that lemma's proposition by
construction), and the conclusion is written without the scratch file's notations: any two
distinct real ordinates `t`, `t'` at which the completed L-function of the row `ω` has a zero of
finite order on the line `Re = a` satisfy `1 ≤ C (1 + |t|)^N |t - t'|`. -/
theorem verifier_explicit_gap (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω)) {s : ℝ} (hs : 1 < s) (hs3 : 3 < s)
    (ω : PontryaginDual C₁)
    (hlemma : ∀ (φ : BruhatCompactSupport C𝔽)
      (x : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a 0 s → Q(a, hStrip(h₀), hs₀(hs)))
      (Λ : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a 0 s →
        StrongDual ℂ Q(a, hStrip(h₀), hs₀(hs)))
      (hb : IsSpectralMarkushevichBasis x Λ)
      (hj : ∀ j, spectralSobolevDualEmbedding F a hStrip(h₀) hs₀(hs) (Λ j) =
        (spectralStripJet_memLp (F := F) (fun ω ↦ χ ω) h₀ hs₀(hs) j).toLp
          (spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2)),
      type_of% (spectralStripConvolution_traceCauchy_compact_block_series
        a χ hχ h₀ hs φ x Λ hb hj)) :
    ∃ (C : ℝ) (N : ℕ), ∀ t t' : ℝ, t ≠ t' →
      0 < meromorphicOrderAt (continuedCompletedHeckeL (F := F) (χ ω))
        ((a : ℂ) + (t : ℂ) * Complex.I) →
      meromorphicOrderAt (continuedCompletedHeckeL (F := F) (χ ω))
        ((a : ℂ) + (t : ℂ) * Complex.I) ≠ ⊤ →
      0 < meromorphicOrderAt (continuedCompletedHeckeL (F := F) (χ ω))
        ((a : ℂ) + (t' : ℂ) * Complex.I) →
      meromorphicOrderAt (continuedCompletedHeckeL (F := F) (χ ω))
        ((a : ℂ) + (t' : ℂ) * Complex.I) ≠ ⊤ →
      1 ≤ C * (1 + |t|) ^ N * |t - t'| := by
  obtain ⟨C, N, h⟩ := referee_strip_zero_width_gap_of_statement a χ hχ hs hs3 ω
    (fun φ x Λ hb hj ↦ hlemma φ x Λ hb hj)
  refine ⟨C, N, fun t t' hne h1 h1' h2 h2' ↦ ?_⟩
  have hmem (u : ℝ) (hu : 0 < meromorphicOrderAt (continuedCompletedHeckeL (F := F) (χ ω))
      ((a : ℂ) + (u : ℂ) * Complex.I)) :
      (0 : ℝ) ∈ Icc (-(0 : ℝ)) 0 ∧ 0 < order(χ ω, shift(a + (0 : ℝ), u)) := by
    refine ⟨by simp, ?_⟩
    rw [add_zero]
    exact hu
  have hfin (u : ℝ) (hu : meromorphicOrderAt (continuedCompletedHeckeL (F := F) (χ ω))
      ((a : ℂ) + (u : ℂ) * Complex.I) ≠ ⊤) : order(χ ω, shift(a + (0 : ℝ), u)) ≠ ⊤ := by
    rw [add_zero]
    exact hu
  let z : Zs(χ, (0 : ℝ)) := ⟨(ω, 0, t), hmem t h1⟩
  let z' : Zs(χ, (0 : ℝ)) := ⟨(ω, 0, t'), hmem t' h2⟩
  have hz : 0 < Ns(χ, (0 : ℝ), s, z) := verifier_Ns_pos a χ hs3 z (hfin t h1')
  have hz' : 0 < Ns(χ, (0 : ℝ), s, z') := verifier_Ns_pos a χ hs3 z' (hfin t' h2')
  have hzz : z' ≠ z := fun hEq ↦
    hne (congrArg (fun q : Zs(χ, (0 : ℝ)) ↦ q.val.2.2) hEq).symm
  exact h z z' hz hz' rfl rfl hzz

#print axioms verifier_explicit_gap

/-- The hypothesis of `verifier_explicit_gap` is met by the library lemma (with its `sorry`). -/
theorem verifier_explicit_gap_check (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω)) {s : ℝ} (hs : 1 < s) (hs3 : 3 < s)
    (ω : PontryaginDual C₁) :
    ∃ (C : ℝ) (N : ℕ), ∀ t t' : ℝ, t ≠ t' →
      0 < meromorphicOrderAt (continuedCompletedHeckeL (F := F) (χ ω))
        ((a : ℂ) + (t : ℂ) * Complex.I) →
      meromorphicOrderAt (continuedCompletedHeckeL (F := F) (χ ω))
        ((a : ℂ) + (t : ℂ) * Complex.I) ≠ ⊤ →
      0 < meromorphicOrderAt (continuedCompletedHeckeL (F := F) (χ ω))
        ((a : ℂ) + (t' : ℂ) * Complex.I) →
      meromorphicOrderAt (continuedCompletedHeckeL (F := F) (χ ω))
        ((a : ℂ) + (t' : ℂ) * Complex.I) ≠ ⊤ →
      1 ≤ C * (1 + |t|) ^ N * |t - t'| :=
  verifier_explicit_gap a χ hχ hs hs3 ω (fun φ x Λ hb hj ↦
    spectralStripConvolution_traceCauchy_compact_block_series a χ hχ h₀ hs φ x Λ hb hj)

#print axioms verifier_explicit_gap_check

end VerifierStrip

section VerifierLine

variable (a : ℝ)

local notation "Zl(" χ ")" => {z : PontryaginDual C₁ × ℝ // 0 < order(χ z.1, shift(a, z.2))}
local notation "Nl(" χ ", " s ", " z ")" => spectralBoundaryMultiplicity s (mult(χ (z).val.1,
  shift(a, (z).val.2)))

/-- On the line: for `s > 3` every zero of finite order has a surviving zeroth jet. -/
theorem verifier_Nl_pos (χ : PontryaginDual C₁ → PontryaginDual C𝔽) {s : ℝ} (hs3 : 3 < s)
    (z : Zl(χ)) (hfin : order(χ z.val.1, shift(a, z.val.2)) ≠ ⊤) : 0 < Nl(χ, s, z) := by
  have key : ∀ o : WithTop ℤ, 0 < o → o ≠ ⊤ → 0 < o.untop₀.toNat := by
    intro o hpos hfin
    cases o with
    | top => exact absurd rfl hfin
    | coe n =>
      rw [WithTop.untop₀_coe]
      have hn : (0 : ℤ) < n := by exact_mod_cast hpos
      omega
  have hk : 0 < mult(χ z.val.1, shift(a, z.val.2)) := key _ z.property hfin
  unfold spectralBoundaryMultiplicity
  exact lt_min hk (Nat.ceil_pos.mpr (by linarith))

#print axioms verifier_Nl_pos

open Classical in
/-- The line version, restated by the verifier: hypothesis by `type_of%` from the library's line
residue lemma (as it stands at b4574b0), conclusion without the scratch file's notations. -/
theorem verifier_explicit_line_gap (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice (F := F) χ) {s : ℝ} (hs : 1 < s) (hs3 : 3 < s)
    (ω : PontryaginDual C₁)
    (hlemma : ∀ (φ : BruhatCompactSupport C𝔽) (eχ : PontryaginDual C₁ ↪ ℕ)
      (e : Zl(χ) ↪ ℕ × ℕ) (he : ∀ z, (e z).1 = eχ z.val.1)
      (Λ : SpectralLineJetIndex (F := F) χ a s → StrongDual ℂ Q(a, h₀, hs₀(hs)))
      (hj : ∀ j, spectralSobolevDualEmbedding F a h₀ hs₀(hs) (Λ j) =
        (spectralLineJet_memLp (F := F) χ hs j).toLp
          (spectralZeroJet (F := F) (χ j.val.1) 0 j.val.2.1 j.val.2.2)),
      type_of% (spectralLineConvolution_traceCauchy_scalar_shell (F := F)
        a χ hχ hs φ eχ e he Λ hj)) :
    ∃ (C : ℝ) (N : ℕ), ∀ t t' : ℝ, t ≠ t' →
      0 < meromorphicOrderAt (continuedCompletedHeckeL (F := F) (χ ω))
        ((a : ℂ) + (t : ℂ) * Complex.I) →
      meromorphicOrderAt (continuedCompletedHeckeL (F := F) (χ ω))
        ((a : ℂ) + (t : ℂ) * Complex.I) ≠ ⊤ →
      0 < meromorphicOrderAt (continuedCompletedHeckeL (F := F) (χ ω))
        ((a : ℂ) + (t' : ℂ) * Complex.I) →
      meromorphicOrderAt (continuedCompletedHeckeL (F := F) (χ ω))
        ((a : ℂ) + (t' : ℂ) * Complex.I) ≠ ⊤ →
      1 ≤ C * (1 + |t|) ^ N * |t - t'| := by
  obtain ⟨C, N, h⟩ := referee_line_gap_of_statement a χ hχ hs hs3 ω
    (fun φ eχ e he Λ hj ↦ hlemma φ eχ e he Λ hj)
  refine ⟨C, N, fun t t' hne h1 h1' h2 h2' ↦ ?_⟩
  let z : Zl(χ) := ⟨(ω, t), h1⟩
  let z' : Zl(χ) := ⟨(ω, t'), h2⟩
  have hz : 0 < Nl(χ, s, z) := verifier_Nl_pos a χ hs3 z h1'
  have hz' : 0 < Nl(χ, s, z') := verifier_Nl_pos a χ hs3 z' h2'
  have hzz : z' ≠ z := fun hEq ↦ hne (congrArg (fun q : Zl(χ) ↦ q.val.2) hEq).symm
  exact h z z' hz hz' rfl rfl hzz

#print axioms verifier_explicit_line_gap

end VerifierLine

/-! ### Library declarations the statements rest on -/

#print axioms spectralStripConvolution_traceCauchy_compact_block_series
#print axioms spectralLineConvolution_traceCauchy_scalar_shell
#print axioms completedHeckeL_exists_continuation
#print axioms continuedCompletedHeckeL_spec
#print axioms spectralStripMultiplicity
#print axioms spectralConvolution
#print axioms spectralSobolevDualEmbedding_isometry_range
#print axioms spectralStripConvolution_traceCauchy_scalar_bound
#print axioms spectralStripConvolution_jet_top
#print axioms spectralLineMarkushevichBasis
#print axioms spectralStripConvolution_traceCauchy
#print axioms spectralLineConvolution_traceCauchy

end RiemannMasullo
