module
import all RiemannMasullo.Ch10_TraceSpectral.Sec2
import all RiemannMasullo.Ch03_IdelicZeta.Sec2
import RiemannMasullo.Ch13_ZerosHecke.Targets
import RiemannMasullo.Ch13_ZerosHecke.RationalExteriorZeros
import all RiemannMasullo.ForMathlib.NumberTheory.NumberField.DedekindZeta.MultipleZero

/-!
# What `spectralStripJet_order_and_margin_locally_finite_multiple_zeros` implies

Scratch file for the referee's report on issue #7220 (split from #4987), at commit 5b158be.
Checked with `lake lean .agent/Gap7220.lean` (about 15 s). Nothing here is part of the library.
The `import all` lines give access to private lemmas of three library files; they are for this
scratch file only.

Main statements (all with axioms `propext`, `Classical.choice`, `Quot.sound` only):

* `locallyFinite_iff`: the target for all `x` ⟺ bounded multiplicities and finitely many
  vertical lines of multiple zeros, for the chosen base points.
* `order_eq_basepoint'`: in `Re s > 0` every unitary character has the zeros of the base point
  of its component, translated vertically; so the target is about all Hecke L-functions:
  `locallyFinite_iff_all_characters` states it without the base points.
* `locallyFinite_iff_bounded_of_GRH`: granting the statement of `heckeL_zero_re_eq_half`, the
  target is equivalent to bounded multiplicities on the critical line.
* `riemannZeta_multiplicity_bounded_near_critical_line`: the target over `ℚ` at `x = 1/2`
  bounds the multiplicities of the zeros of Riemann zeta near the critical line.
* `rat_locallyFinite_iff_dirichlet`: over `ℚ` the target is equivalent to a statement about
  primitive Dirichlet L-functions.
* `cubic_zero_free_strip`: the target at `x = 1` for the splitting field of `X³ − 2` gives a
  zero-free strip for the quotient of the zeta function of `ℚ(∛2)` by Riemann zeta.
* `rat_locallyFinite_of_simple_zeros`: over `ℚ` the target follows from the simplicity of the
  zeros of the primitive Dirichlet L-functions.
* `riemannZeta_multiplicity_bounded_of_upperBound`: one instance over `ℚ` of the uniform norm
  bound of Proposition 10.2.2.2 already bounds the multiplicities of all zeta zeros;
  `riemannZeta_critical_line_multiplicity_bounded_of_line_upperBound` needs only the jets on the
  central line of the strip.

The theorems named `…_from_target`, `…_from_gap`, `…_from_proposition`, `…_from_corollary`
apply these to the library as it stands; they depend on `sorryAx` through the private lemma.
-/

noncomputable section

open Filter Function NumberField Set
open scoped Topology NNReal NumberField.AdeleRing

namespace RiemannMasullo.Gap7220

set_option quotPrecheck false

variable {F : Type*} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "restriction" =>
  (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : C₁ →ₜ* C𝔽)
local notation "shift(" b ", " t ")" => ((b : ℝ) : ℂ) + (t : ℂ) * Complex.I
local notation "multiplicity(" χ ", " z ")" =>
  (meromorphicOrderAt (continuedCompletedHeckeL χ) z).untop₀.toNat
local notation "halfPlane" => Complex.re ⁻¹' Ioi (1 : ℝ)

/-- The conclusion of the target lemma at one real number `x`, word for word. -/
def LocallyFiniteAt (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (x : ℝ) : Prop :=
  ∃ U ∈ 𝓝 x, {p : ℝ × ℕ | p.1 ∈ U ∧ 1 < p.2 ∧ ∃ (ω : PontryaginDual C₁) (t : ℝ),
    multiplicity(χ ω, shift(p.1, t)) = p.2}.Finite

/-- `LocallyFiniteAt` is the statement of the private lemma (this is its only use here). -/
theorem locallyFiniteAt_of_target (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice χ) (x : ℝ) : LocallyFiniteAt χ x :=
  spectralStripJet_order_and_margin_locally_finite_multiple_zeros χ hχ x

/-! ## The zeros do not depend on the base point, up to a vertical translation -/

/-- An imaginary norm twist translates the zeros and poles in the right half-plane. -/
theorem order_of_normTwist (ψ θ : PontryaginDual C𝔽) (a : ℂ) (ha : a.re = 0)
    (hψ : ideleClassNormTwist ψ 0 = ideleClassNormTwist θ a) {s : ℂ} (hs : 0 < s.re) :
    meromorphicOrderAt (continuedCompletedHeckeL ψ) s =
      meromorphicOrderAt (continuedCompletedHeckeL θ) (s + a) := by
  obtain ⟨g, hg, hgeq⟩ := finiteHeckeL_exists_continuation θ
  have hsa : 0 < (s + a).re := by rw [Complex.add_re, ha, add_zero]; exact hs
  have h1 := meromorphicOrderAt_finiteHeckeL_continuation θ hg.meromorphicOn hgeq hsa
  have hf : MeromorphicOn (g ∘ (fun w : ℂ ↦ w + a)) univ := fun z _ ↦
    MeromorphicAt.comp_analyticAt (f := g) (g := fun w : ℂ ↦ w + a) (x := z)
      (hg.meromorphicOn (z + a) (mem_univ _)) (by fun_prop)
  have h2 := meromorphicOrderAt_finiteHeckeL_continuation ψ hf (fun z ↦ by
    change g ((z : ℂ) + a) = finiteHeckeL ψ z
    rw [finiteHeckeL_imaginary_twist θ ψ a ha hψ z]
    exact hgeq (⟨(z : ℂ) + a, _⟩ : halfPlane)) hs
  rw [← h2, ← h1]
  exact meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt (f := g) (c := a) (x := s)

/-- Every unitary character of the idele class group has the zeros of the chosen base point
of its component, moved vertically. -/
theorem order_eq_basepoint' {χ : PontryaginDual C₁ → PontryaginDual C𝔽}
    (hχ : IsSpectralBasepointChoice χ) (ψ : PontryaginDual C𝔽) :
    ∃ τ : ℝ, ∀ σ t : ℝ, 0 < σ →
      meromorphicOrderAt (continuedCompletedHeckeL ψ) (shift(σ, t)) =
        meromorphicOrderAt (continuedCompletedHeckeL (χ (ψ.comp restriction)))
          (shift(σ, (t + τ : ℝ))) := by
  let ω : PontryaginDual C₁ := ψ.comp restriction
  obtain ⟨z, hz, -⟩ := hχ.existsUnique_normTwist ω (ideleClassNormTwist ψ 0) (fun g ↦ by
    change (ψ g.val : ℂ) * _ ^ (0 : ℂ) = _
    rw [Complex.cpow_zero, mul_one]
    rfl)
  have hre : z.re = 0 := by
    have h1 := quasiCharacterAbscissa_ideleClassNormTwist ψ 0
    have h2 := quasiCharacterAbscissa_ideleClassNormTwist (χ ω) z
    rw [← hz, h1] at h2
    simpa using h2.symm
  refine ⟨z.im, fun σ t hσ ↦ ?_⟩
  have hs : 0 < (shift(σ, t)).re := by simpa using hσ
  rw [order_of_normTwist ψ (χ ω) z hre hz hs]
  congr 1
  apply Complex.ext <;> simp [hre]

/-- The same, without naming the component. -/
theorem order_eq_basepoint {χ : PontryaginDual C₁ → PontryaginDual C𝔽}
    (hχ : IsSpectralBasepointChoice χ) (ψ : PontryaginDual C𝔽) :
    ∃ (ω : PontryaginDual C₁) (τ : ℝ), ∀ σ t : ℝ, 0 < σ →
      meromorphicOrderAt (continuedCompletedHeckeL ψ) (shift(σ, t)) =
        meromorphicOrderAt (continuedCompletedHeckeL (χ ω)) (shift(σ, (t + τ : ℝ))) :=
  ⟨_, order_eq_basepoint' hχ ψ⟩

/-! ## Consequences of the conclusion at one real number -/

/-- The pair of a real part and a multiplicity above one belongs to the set of the lemma. -/
theorem mem_pairs (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (U : Set ℝ)
    (ω : PontryaginDual C₁) (σ t : ℝ) (hσ : σ ∈ U)
    (hn : 1 < multiplicity(χ ω, shift(σ, t))) :
    (σ, multiplicity(χ ω, shift(σ, t))) ∈
      {p : ℝ × ℕ | p.1 ∈ U ∧ 1 < p.2 ∧ ∃ (ω : PontryaginDual C₁) (t : ℝ),
        multiplicity(χ ω, shift(p.1, t)) = p.2} :=
  ⟨hσ, hn, ω, t, rfl⟩

/-- Near `x`, one integer bounds the multiplicities of the zeros with positive real part of
the completed L-functions of all unitary characters, not only of the chosen base points. -/
theorem bounded_of_locallyFiniteAt {χ : PontryaginDual C₁ → PontryaginDual C𝔽}
    (hχ : IsSpectralBasepointChoice χ) {x : ℝ} (h : LocallyFiniteAt χ x) :
    ∃ U ∈ 𝓝 x, ∃ M : ℕ, ∀ (ψ : PontryaginDual C𝔽) (σ t : ℝ), σ ∈ U → 0 < σ →
      multiplicity(ψ, shift(σ, t)) ≤ M := by
  obtain ⟨U, hU, hfin⟩ := h
  obtain ⟨K, hK⟩ := (hfin.image Prod.snd).bddAbove
  refine ⟨U, hU, max K 1, fun ψ σ t hσU hσ ↦ ?_⟩
  obtain ⟨ω, τ, hτ⟩ := order_eq_basepoint hχ ψ
  rw [hτ σ t hσ]
  by_cases hn : 1 < multiplicity(χ ω, shift(σ, (t + τ : ℝ)))
  · exact (hK (mem_image_of_mem Prod.snd (mem_pairs χ U ω σ (t + τ) hσU hn))).trans
      (le_max_left _ _)
  · exact (not_lt.mp hn).trans (le_max_right _ _)

/-- Near `x`, the multiple zeros with positive real part of the completed L-functions of all
unitary characters lie on finitely many vertical lines. -/
theorem finite_re_of_locallyFiniteAt {χ : PontryaginDual C₁ → PontryaginDual C𝔽}
    (hχ : IsSpectralBasepointChoice χ) {x : ℝ} (h : LocallyFiniteAt χ x) :
    ∃ U ∈ 𝓝 x, {σ : ℝ | σ ∈ U ∧ 0 < σ ∧ ∃ (ψ : PontryaginDual C𝔽) (t : ℝ),
      1 < multiplicity(ψ, shift(σ, t))}.Finite := by
  obtain ⟨U, hU, hfin⟩ := h
  refine ⟨U, hU, (hfin.image Prod.fst).subset ?_⟩
  rintro σ ⟨hσU, hσ, ψ, t, hn⟩
  obtain ⟨ω, τ, hτ⟩ := order_eq_basepoint hχ ψ
  rw [hτ σ t hσ] at hn
  exact mem_image_of_mem Prod.fst (mem_pairs χ U ω σ (t + τ) hσU hn)

/-! ## The target is no stronger than the recorded gap it was split from -/

/-- The strip estimate of `spectralStripJet_order_and_margin`, at the single Sobolev exponent 2
and half-width 1 and for all centers, implies the conclusion of the target. This is the check
of mccorvie in the split report on issue #4987, with the conclusion written as
`LocallyFiniteAt`. -/
theorem locallyFiniteAt_of_unit_strips (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (h : ∀ a : ℝ, ∃ (K : ℕ) (δ : ℝ), 0 < δ ∧ ∀ j : SpectralStripJetIndex χ a 1 2,
      j.val.2.2.2 ≤ K ∧ ((2 - 1) / 2 ≤ (j.val.2.2.2 : ℝ) → |j.val.2.1| ≤ 1 - δ))
    (x : ℝ) : LocallyFiniteAt χ x := by
  classical
  choose K δ hδ hj using h
  have atZero (c y t : ℝ) (ω : PontryaginDual C₁) (n : ℕ)
      (hn : multiplicity(χ ω, shift(y, t)) = n) (hm : 1 < n) (hi : |y - c| < 1) :
      n ≤ K c + 1 ∧ |y - c| ≤ 1 - δ c := by
    let j : SpectralStripJetIndex χ c 1 2 := ⟨(ω, y - c, t, n - 1), by
      change n - 1 < spectralStripMultiplicity 1 2 (y - c)
        (multiplicity(χ ω, shift(c + (y - c), t)))
      rw [spectralStripMultiplicity_interior (abs_lt.mp hi), show c + (y - c) = y by ring, hn]
      omega⟩
    obtain ⟨hK, hd⟩ := hj c j
    change n - 1 ≤ K c at hK
    refine ⟨by omega, hd ?_⟩
    change ((2 : ℝ) - 1) / 2 ≤ ((n - 1 : ℕ) : ℝ)
    have h1 : (1 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ n - 1)
    linarith
  let r (x : ℝ) := min 1 (min (δ (x - 1)) (δ (x + 1)))
  let U (x : ℝ) := Ioo (x - r x) (x + r x)
  have hU (x : ℝ) : U x ∈ 𝓝 x := by
    have hr : 0 < r x := lt_min one_pos (lt_min (hδ _) (hδ _))
    exact Ioo_mem_nhds (by linarith) (by linarith)
  refine ⟨U x, hU x, ?_⟩
  apply ((finite_singleton x).prod (finite_Iic (K x + 1))).subset
  rintro ⟨y, n⟩ ⟨hxy, hm, ω, t, hn⟩
  obtain ⟨hxl, hxr⟩ : x - r x < y ∧ y < x + r x := hxy
  have hr1 : r x ≤ 1 := min_le_left _ _
  have hrL : r x ≤ δ (x - 1) := (min_le_right _ _).trans (min_le_left _ _)
  have hrR : r x ≤ δ (x + 1) := (min_le_right _ _).trans (min_le_right _ _)
  have heq : y = x := by
    rcases lt_trichotomy y x with hlt | heq | hgt
    · have hsep := (atZero (x - 1) y t ω n hn hm (abs_lt.mpr ⟨by linarith, by linarith⟩)).2
      linarith [(le_abs_self (y - (x - 1)))]
    · exact heq
    · have hsep := (atZero (x + 1) y t ω n hn hm (abs_lt.mpr ⟨by linarith, by linarith⟩)).2
      linarith [neg_le_abs (y - (x + 1))]
  subst y
  exact ⟨rfl, (atZero x x t ω n hn hm (by simp)).1⟩

/-! ## Where the zeros are, and finiteness of the orders -/

/-- The truncated order vanishes when the order is not positive. -/
theorem toNat_untop₀_eq_zero {o : WithTop ℤ} (h : ¬ 0 < o) : o.untop₀.toNat = 0 := by
  cases o with
  | top => exact absurd (WithTop.coe_lt_top 0) h
  | coe n =>
    rw [WithTop.untop₀_coe]
    have hn : ¬ (0 : ℤ) < n := fun hn ↦ h (by exact_mod_cast hn)
    omega

/-- The completed L-function does not vanish to the right of one. -/
theorem continuedCompletedHeckeL_ne_zero (ψ : PontryaginDual C𝔽) {w : ℂ} (hw : 1 < w.re) :
    continuedCompletedHeckeL ψ w ≠ 0 := by
  rw [show continuedCompletedHeckeL ψ w = completedHeckeL ψ ⟨w, hw⟩ from
    (continuedCompletedHeckeL_spec ψ).2 ⟨w, hw⟩]
  exact mul_ne_zero (heckeGammaFactor_ne_zero_of_re_pos ψ (zero_lt_one.trans hw))
    (finiteHeckeL_ne_zero_of_one_lt_re ψ ⟨w, hw⟩)

/-- The completed L-function vanishes identically nowhere: every order is finite. -/
theorem order_ne_top (ψ : PontryaginDual C𝔽) (s : ℂ) :
    meromorphicOrderAt (continuedCompletedHeckeL ψ) s ≠ ⊤ := by
  have hspec := continuedCompletedHeckeL_spec ψ
  have h2 : meromorphicOrderAt (continuedCompletedHeckeL ψ) 2 ≠ ⊤ := by
    rw [(hspec.1 (mem_univ 2)).meromorphicOrderAt_eq_zero_iff.mpr
      (continuedCompletedHeckeL_ne_zero ψ (by norm_num))]
    exact WithTop.coe_ne_top
  exact hspec.1.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (mem_univ _) (mem_univ _) h2

/-- There are no zeros outside the closed critical strip. The argument is the one in the
report of sergmister on issue #4987 (functional equation and Euler product). -/
theorem multiplicity_eq_zero_outside (ψ : PontryaginDual C𝔽) (s : ℂ)
    (hs : s.re ∉ Icc (0 : ℝ) 1) : multiplicity(ψ, s) = 0 := by
  have hval : continuedCompletedHeckeL ψ s ≠ 0 := by
    rcases lt_or_ge s.re 0 with hneg | hn
    · obtain ⟨ε, _, _, he⟩ := completedHeckeL_continuation_functionalEquation ψ _ _
        (continuedCompletedHeckeL_spec _).1 (continuedCompletedHeckeL_spec _).2
        (continuedCompletedHeckeL_spec _).1 (continuedCompletedHeckeL_spec _).2
      have hw : 1 < (1 - s).re := by
        simp only [Complex.sub_re, Complex.one_re]
        linarith
      intro h0
      exact continuedCompletedHeckeL_ne_zero ψ⁻¹ hw (by rw [he s, h0, mul_zero])
    · exact continuedCompletedHeckeL_ne_zero ψ (lt_of_not_ge fun h ↦ hs ⟨hn, h⟩)
  have ho := ((continuedCompletedHeckeL_spec ψ).1
    (mem_univ s)).meromorphicOrderAt_eq_zero_iff.mpr hval
  rw [ho]
  rfl

/-- The functional equation reflects the orders. -/
theorem order_reflect (ψ : PontryaginDual C𝔽) (z : ℂ) :
    meromorphicOrderAt (continuedCompletedHeckeL ψ⁻¹) (1 - z) =
      meromorphicOrderAt (continuedCompletedHeckeL ψ) z := by
  obtain ⟨hL, ha⟩ := continuedCompletedHeckeL_spec ψ
  obtain ⟨hL', ha'⟩ := continuedCompletedHeckeL_spec ψ⁻¹
  obtain ⟨ε, hε, hne, hfe⟩ :=
    completedHeckeL_continuation_functionalEquation ψ _ _ hL ha hL' ha'
  have hc := meromorphicOrderAt_comp_of_deriv_ne_zero (f := continuedCompletedHeckeL ψ⁻¹)
    (show AnalyticAt ℂ (fun s : ℂ ↦ 1 - s) z by fun_prop)
    (show deriv (fun s : ℂ ↦ 1 - s) z ≠ 0 by simp)
  rw [show continuedCompletedHeckeL ψ⁻¹ ∘ (fun s : ℂ ↦ 1 - s) =
      ε * continuedCompletedHeckeL ψ from funext hfe,
    meromorphicOrderAt_mul_of_ne_zero (hε.analyticAt z) (hne z)] at hc
  exact hc.symm

/-- All zeros lie in the open critical strip. -/
theorem multiplicity_eq_zero_outside_open (ψ : PontryaginDual C𝔽) (s : ℂ)
    (hs : s.re ∉ Ioo (0 : ℝ) 1) : multiplicity(ψ, s) = 0 := by
  apply toNat_untop₀_eq_zero
  intro hpos
  rcases le_or_gt s.re 0 with h0 | h0
  · rw [← order_reflect ψ s] at hpos
    have hre : 0 < (1 - s).re := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    have hlt := completedHeckeL_continuation_zeros ψ⁻¹ _ (continuedCompletedHeckeL_spec _).1
      (continuedCompletedHeckeL_spec _).2 hre hpos
    simp only [Complex.sub_re, Complex.one_re] at hlt
    linarith
  · have hlt := completedHeckeL_continuation_zeros ψ _ (continuedCompletedHeckeL_spec _).1
      (continuedCompletedHeckeL_spec _).2 h0 hpos
    exact hs ⟨h0, hlt⟩

/-! ## The lemma for all `x` is an arithmetic statement about one field -/

/-- **Exact content of the target.** The conclusion for every real `x` holds if and only if
one integer bounds all the multiplicities and the multiple zeros lie on finitely many vertical
lines. No hypothesis on the base points is used. -/
theorem locallyFinite_iff (χ : PontryaginDual C₁ → PontryaginDual C𝔽) :
    (∀ x : ℝ, LocallyFiniteAt χ x) ↔
      (∃ M : ℕ, ∀ (ω : PontryaginDual C₁) (σ t : ℝ), multiplicity(χ ω, shift(σ, t)) ≤ M) ∧
      {σ : ℝ | ∃ (ω : PontryaginDual C₁) (t : ℝ),
        1 < multiplicity(χ ω, shift(σ, t))}.Finite := by
  constructor
  · intro h
    choose U hU hfin using h
    obtain ⟨T, -, hcover⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).elim_nhds_subcover U
      (fun x _ ↦ hU x)
    have hall : {p : ℝ × ℕ | 1 < p.2 ∧ ∃ (ω : PontryaginDual C₁) (t : ℝ),
        multiplicity(χ ω, shift(p.1, t)) = p.2}.Finite := by
      apply (T.finite_toSet.biUnion fun x _ ↦ hfin x).subset
      rintro ⟨σ, n⟩ ⟨hn, ω, t, hm⟩
      have hσ : σ ∈ Icc (0 : ℝ) 1 := by
        by_contra hout
        have hre : (shift(σ, t)).re = σ := by simp
        have h0 := multiplicity_eq_zero_outside (χ ω) (shift(σ, t)) (by rwa [hre])
        change multiplicity(χ ω, shift(σ, t)) = n at hm
        change 1 < n at hn
        omega
      obtain ⟨x, hxT, hxU⟩ := mem_iUnion₂.mp (hcover hσ)
      exact mem_iUnion₂.mpr ⟨x, hxT, hxU, hn, ω, t, hm⟩
    constructor
    · obtain ⟨K, hK⟩ := (hall.image Prod.snd).bddAbove
      refine ⟨max K 1, fun ω σ t ↦ ?_⟩
      by_cases hn : 1 < multiplicity(χ ω, shift(σ, t))
      · exact (hK (mem_image_of_mem Prod.snd
          (show (σ, multiplicity(χ ω, shift(σ, t))) ∈ _ from ⟨hn, ω, t, rfl⟩))).trans
          (le_max_left _ _)
      · exact (not_lt.mp hn).trans (le_max_right _ _)
    · apply (hall.image Prod.fst).subset
      rintro σ ⟨ω, t, hn⟩
      exact ⟨(σ, multiplicity(χ ω, shift(σ, t))), ⟨hn, ω, t, rfl⟩, rfl⟩
  · rintro ⟨⟨M, hM⟩, hfin⟩ x
    refine ⟨univ, univ_mem, (hfin.prod (finite_Iic M)).subset ?_⟩
    rintro ⟨σ, n⟩ ⟨-, hn, ω, t, hm⟩
    change multiplicity(χ ω, shift(σ, t)) = n at hm
    change 1 < n at hn
    refine ⟨⟨ω, t, ?_⟩, ?_⟩
    · change 1 < multiplicity(χ ω, shift(σ, t))
      omega
    · change n ≤ M
      exact hm ▸ hM ω σ t

/-! ## Global consequences for all unitary characters of the field -/

/-- One integer bounds the multiplicities of all zeros with positive real part of the completed
L-functions of all unitary characters of the idele class group. -/
theorem bounded_of_locallyFinite {χ : PontryaginDual C₁ → PontryaginDual C𝔽}
    (hχ : IsSpectralBasepointChoice χ) (h : ∀ x : ℝ, LocallyFiniteAt χ x) :
    ∃ M : ℕ, ∀ (ψ : PontryaginDual C𝔽) (s : ℂ), 0 < s.re → multiplicity(ψ, s) ≤ M := by
  choose U hU M hM using fun x ↦ bounded_of_locallyFiniteAt hχ (h x)
  obtain ⟨T, -, hcover⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).elim_nhds_subcover U
    (fun x _ ↦ hU x)
  refine ⟨T.sup M, fun ψ s hs ↦ ?_⟩
  by_cases hstrip : s.re ∈ Icc (0 : ℝ) 1
  · obtain ⟨x, hxT, hxU⟩ := mem_iUnion₂.mp (hcover hstrip)
    have hb := hM x ψ s.re s.im hxU hs
    rw [Complex.re_add_im] at hb
    exact hb.trans (Finset.le_sup (f := M) hxT)
  · rw [multiplicity_eq_zero_outside ψ s hstrip]
    exact Nat.zero_le _

/-- The multiple zeros with positive real part of the completed L-functions of all unitary
characters of the idele class group lie on finitely many vertical lines. -/
theorem finite_re_of_locallyFinite {χ : PontryaginDual C₁ → PontryaginDual C𝔽}
    (hχ : IsSpectralBasepointChoice χ) (h : ∀ x : ℝ, LocallyFiniteAt χ x) :
    {σ : ℝ | 0 < σ ∧ ∃ (ψ : PontryaginDual C𝔽) (t : ℝ),
      1 < multiplicity(ψ, shift(σ, t))}.Finite := by
  choose U hU hfin using fun x ↦ finite_re_of_locallyFiniteAt hχ (h x)
  obtain ⟨T, -, hcover⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).elim_nhds_subcover U
    (fun x _ ↦ hU x)
  apply (T.finite_toSet.biUnion fun x _ ↦ hfin x).subset
  rintro σ ⟨hσ, ψ, t, hn⟩
  have hstrip : σ ∈ Icc (0 : ℝ) 1 := by
    by_contra hout
    have hre : (shift(σ, t)).re = σ := by simp
    have h0 := multiplicity_eq_zero_outside ψ (shift(σ, t)) (by rwa [hre])
    omega
  obtain ⟨x, hxT, hxU⟩ := mem_iUnion₂.mp (hcover hstrip)
  exact mem_iUnion₂.mpr ⟨x, hxT, hxU, hσ, ψ, t, hn⟩

/-- **What has to be true, with no reference to the base points.** For any choice of base
points, the target for all `x` holds if and only if one integer bounds the multiplicities of all
zeros with positive real part of the completed L-functions of all unitary characters of the
idele class group, and the multiple ones lie on finitely many vertical lines. The right-hand
side is a property of the field alone. -/
theorem locallyFinite_iff_all_characters {χ : PontryaginDual C₁ → PontryaginDual C𝔽}
    (hχ : IsSpectralBasepointChoice χ) :
    (∀ x : ℝ, LocallyFiniteAt χ x) ↔
      (∃ M : ℕ, ∀ (ψ : PontryaginDual C𝔽) (s : ℂ), 0 < s.re → multiplicity(ψ, s) ≤ M) ∧
      {σ : ℝ | 0 < σ ∧ ∃ (ψ : PontryaginDual C𝔽) (t : ℝ),
        1 < multiplicity(ψ, shift(σ, t))}.Finite := by
  refine ⟨fun h ↦ ⟨bounded_of_locallyFinite hχ h, finite_re_of_locallyFinite hχ h⟩, ?_⟩
  rintro ⟨⟨M, hM⟩, hfin⟩
  apply (locallyFinite_iff χ).mpr
  constructor
  · refine ⟨M, fun ω σ t ↦ ?_⟩
    by_cases hσ : σ ∈ Ioo (0 : ℝ) 1
    · exact hM (χ ω) _ (by simpa using hσ.1)
    · rw [multiplicity_eq_zero_outside_open (χ ω) (shift(σ, t)) (by simpa using hσ)]
      exact Nat.zero_le _
  · apply hfin.subset
    rintro σ ⟨ω, t, hn⟩
    have hσ : σ ∈ Ioo (0 : ℝ) 1 := by
      by_contra hout
      have h0 := multiplicity_eq_zero_outside_open (χ ω) (shift(σ, t)) (by simpa using hout)
      omega
    exact ⟨hσ.1, χ ω, t, hn⟩

/-- **Granting the generalized Riemann hypothesis for the Hecke L-functions of the field, the
target is equivalent to a bound for the multiplicities of the zeros on the critical line.** The
hypothesis is the statement of the library's `heckeL_zero_re_eq_half`. The Riemann hypothesis
does not supply such a bound. -/
theorem locallyFinite_iff_bounded_of_GRH {χ : PontryaginDual C₁ → PontryaginDual C𝔽}
    (hχ : IsSpectralBasepointChoice χ)
    (hGRH : ∀ (ψ : PontryaginDual C𝔽) (s : ℂ), 0 < s.re → s.re < 1 →
      0 < meromorphicOrderAt (continuedCompletedHeckeL ψ) s → s.re = 1 / 2) :
    (∀ x : ℝ, LocallyFiniteAt χ x) ↔
      ∃ M : ℕ, ∀ (ψ : PontryaginDual C𝔽) (t : ℝ),
        multiplicity(ψ, shift((1 / 2 : ℝ), t)) ≤ M := by
  -- a zero has real part one half
  have hline (ψ : PontryaginDual C𝔽) (s : ℂ) (hpos : 0 < multiplicity(ψ, s)) :
      s.re = 1 / 2 := by
    have hstrip : s.re ∈ Ioo (0 : ℝ) 1 := by
      by_contra hout
      have h0 := multiplicity_eq_zero_outside_open ψ s hout
      omega
    refine hGRH ψ s hstrip.1 hstrip.2 ?_
    by_contra hnot
    have h0 := toNat_untop₀_eq_zero hnot
    omega
  rw [locallyFinite_iff_all_characters hχ]
  constructor
  · rintro ⟨⟨M, hM⟩, -⟩
    exact ⟨M, fun ψ t ↦ hM ψ _ (by simp)⟩
  · rintro ⟨M, hM⟩
    constructor
    · refine ⟨M, fun ψ s _ ↦ ?_⟩
      rcases Nat.eq_zero_or_pos (multiplicity(ψ, s)) with h0 | hpos
      · rw [h0]
        exact Nat.zero_le _
      · have hre := hline ψ s hpos
        have hs : s = shift((1 / 2 : ℝ), s.im) := by
          apply Complex.ext <;> simp [hre]
        rw [hs]
        exact hM ψ s.im
    · apply (finite_singleton (1 / 2 : ℝ)).subset
      rintro σ ⟨-, ψ, t, hn⟩
      have hre := hline ψ (shift(σ, t)) (by omega)
      simpa using hre

/-! ## The uniform norm bound of the proposition already bounds the multiplicities -/

section UpperBound

open MeasureTheory

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" =>
  (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "hm𝔽" => (⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ :
  IsModulation m𝔽)
local notation "stripJet(" χ ", " j ")" =>
  spectralZeroJet (χ (j).val.1) (j).val.2.1 (j).val.2.2.1 (j).val.2.2.2

/-- On `[2, 3]` the norm integrand of a jet of order `k`, in a strip of half-width one with
Sobolev exponent two, is at least a fixed multiple of `4 ^ k`. -/
theorem jet_integrand_ge (b : ℝ) (hb : |b| ≤ 1) (k : ℕ) (x : ℝ) (hx : x ∈ Icc (2 : ℝ) 3) :
    Real.exp (-12) * 4 ^ k * (10 : ℝ)⁻¹ ≤
      Real.exp (2 * b * x - 2 * 1 * |x|) * x ^ (2 * k) *
        ((1 + x ^ 2) ^ ((2 : ℝ) / 2))⁻¹ := by
  have hx0 : 0 ≤ x := by linarith [hx.1]
  have hb' := abs_le.mp hb
  have hexp : Real.exp (-12) ≤ Real.exp (2 * b * x - 2 * 1 * |x|) := by
    rw [abs_of_nonneg hx0]
    apply Real.exp_le_exp.mpr
    nlinarith [hx.1, hx.2, hb'.1, hb'.2, mul_nonneg (by linarith : (0 : ℝ) ≤ b + 1) hx0]
  have hpow : (4 : ℝ) ^ k ≤ x ^ (2 * k) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by norm_num) (by nlinarith [hx.1]) k
  have hinv : (10 : ℝ)⁻¹ ≤ ((1 + x ^ 2) ^ ((2 : ℝ) / 2))⁻¹ := by
    rw [show (2 : ℝ) / 2 = 1 by norm_num, Real.rpow_one]
    exact inv_anti₀ (by positivity) (by nlinarith [hx.1, hx.2])
  exact mul_le_mul (mul_le_mul hexp hpow (by positivity) (Real.exp_pos _).le) hinv
    (by positivity) (mul_nonneg (Real.exp_pos _).le (Even.pow_nonneg (even_two_mul _) x))

/-- The norm integral of a jet of order `k` is at least a fixed multiple of `4 ^ k`. -/
theorem jet_integral_ge (b : ℝ) (hb : |b| ≤ 1) (k : ℕ)
    (hint : Integrable (fun x : ℝ ↦ Real.exp (2 * b * x - 2 * 1 * |x|) * x ^ (2 * k) *
      ((1 + x ^ 2) ^ ((2 : ℝ) / 2))⁻¹) volume) :
    Real.exp (-12) * 4 ^ k * (10 : ℝ)⁻¹ ≤
      ∫ x : ℝ, Real.exp (2 * b * x - 2 * 1 * |x|) * x ^ (2 * k) *
        ((1 + x ^ 2) ^ ((2 : ℝ) / 2))⁻¹ ∂volume := by
  have hind_int : Integrable ((Icc (2 : ℝ) 3).indicator fun _ ↦
      Real.exp (-12) * 4 ^ k * (10 : ℝ)⁻¹) volume :=
    (integrableOn_const (by simp)).integrable_indicator measurableSet_Icc
  have hle : ∀ x : ℝ, (Icc (2 : ℝ) 3).indicator (fun _ ↦
      Real.exp (-12) * 4 ^ k * (10 : ℝ)⁻¹) x ≤
      Real.exp (2 * b * x - 2 * 1 * |x|) * x ^ (2 * k) *
        ((1 + x ^ 2) ^ ((2 : ℝ) / 2))⁻¹ := by
    intro x
    by_cases hx : x ∈ Icc (2 : ℝ) 3
    · rw [indicator_of_mem hx]
      exact jet_integrand_ge b hb k x hx
    · rw [indicator_of_notMem hx]
      exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (Even.pow_nonneg (even_two_mul _) x))
        (inv_nonneg.mpr (Real.rpow_pos_of_pos (by positivity) _).le)
  have h1 := integral_mono hind_int hint hle
  have h2 : ∫ x : ℝ, (Icc (2 : ℝ) 3).indicator (fun _ ↦
      Real.exp (-12) * 4 ^ k * (10 : ℝ)⁻¹) x ∂volume = Real.exp (-12) * 4 ^ k * (10 : ℝ)⁻¹ := by
    rw [integral_indicator measurableSet_Icc, setIntegral_const, Real.volume_real_Icc]
    norm_num
  linarith

/-- A strip jet (half-width one, Sobolev exponent two) of norm at most `C` has order at most
an integer depending only on `C` and the field: the norm grows like `2 ^ k` in the order `k`. -/
theorem order_le_of_norm_le (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (a C : ℝ) :
    ∃ K : ℕ, ∀ j : SpectralStripJetIndex χ a 1 2,
      ‖(spectralStripJet_memLp χ zero_le_one zero_le_two j).toLp (stripJet(χ, j))‖ ≤ C →
        j.val.2.2.2 ≤ K := by
  let ν : Measure C𝔽 := canonicalModulatedHaar m𝔽 hm𝔽
  let : ν.IsHaarMeasure := (existsUnique_canonicalModulatedHaar m𝔽 hm𝔽).exists.choose_spec.1
  have hfac_pos : 0 < (Measure.haarScalarFactor μ𝔽 ν : ℝ) := by
    exact_mod_cast (Measure.haarScalarFactor_pos_of_isHaarMeasure μ𝔽 ν)
  refine ⟨⌈C ^ 2 / (Measure.haarScalarFactor μ𝔽 ν : ℝ) /
    (Real.exp (-12) * (10 : ℝ)⁻¹)⌉₊, fun j hjC ↦ ?_⟩
  have hcond : (-1 < j.val.2.1 ∧ j.val.2.1 < 1) ∨
      ((j.val.2.1 = -1 ∨ j.val.2.1 = 1) ∧ 2 * (j.val.2.2.2 : ℝ) + 1 < 2) := by
    have hj := j.property
    unfold spectralStripMultiplicity at hj
    split_ifs at hj with h1 h2
    · exact Or.inl h1
    · refine Or.inr ⟨h2, ?_⟩
      have horder : (j.val.2.2.2 : ℝ) < (2 - 1) / 2 :=
        ((lt_spectralBoundaryMultiplicity 2 _ _).mp hj).2
      linarith
    · omega
  have hf_int := spectralStripJet_integrable (α := 1) (s := 2) zero_le_one zero_le_two hcond
  have hb : |j.val.2.1| ≤ 1 :=
    abs_le.mpr (SpectralStripJetIndex.mem_strip_order_pos zero_le_one j).1
  have hge := jet_integral_ge j.val.2.1 hb j.val.2.2.2 hf_int
  have hsq := spectralStripJet_norm_sq χ zero_le_one zero_le_two j ν rfl
  have hC : ‖(spectralStripJet_memLp χ zero_le_one zero_le_two j).toLp (stripJet(χ, j))‖ ^ 2 ≤
      C ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hjC 2
  rw [hsq] at hC
  have h4 : (4 : ℝ) ^ j.val.2.2.2 ≤ C ^ 2 / (Measure.haarScalarFactor μ𝔽 ν : ℝ) /
      (Real.exp (-12) * (10 : ℝ)⁻¹) := by
    rw [le_div_iff₀ (by positivity), le_div_iff₀ hfac_pos]
    calc (4 : ℝ) ^ j.val.2.2.2 * (Real.exp (-12) * (10 : ℝ)⁻¹) *
          (Measure.haarScalarFactor μ𝔽 ν : ℝ)
        = (Measure.haarScalarFactor μ𝔽 ν : ℝ) *
          (Real.exp (-12) * 4 ^ j.val.2.2.2 * (10 : ℝ)⁻¹) := by ring
      _ ≤ _ := (mul_le_mul_of_nonneg_left hge hfac_pos.le).trans hC
  have hk : (j.val.2.2.2 : ℝ) ≤ 4 ^ j.val.2.2.2 := by
    exact_mod_cast (Nat.lt_pow_self (by norm_num : 1 < 4)).le
  exact Nat.cast_le.mp ((hk.trans h4).trans (Nat.le_ceil _))

/-- A uniform bound for the norms of the strip jets at the center `a`, with half-width one and
Sobolev exponent two, bounds the multiplicities of the zeros of all base points with real part
within one of `a`. -/
theorem multiplicity_bounded_of_upperBound (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (a : ℝ)
    (h : ∃ C : ℝ, ∀ j : SpectralStripJetIndex χ a 1 2,
      ‖(spectralStripJet_memLp χ zero_le_one zero_le_two j).toLp (stripJet(χ, j))‖ ≤ C) :
    ∃ M : ℕ, ∀ (ω : PontryaginDual C₁) (σ t : ℝ), |σ - a| < 1 →
      multiplicity(χ ω, shift(σ, t)) ≤ M := by
  obtain ⟨C, hC⟩ := h
  obtain ⟨K, hK⟩ := order_le_of_norm_le χ a C
  refine ⟨K + 1, fun ω σ t hσ ↦ ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  let j : SpectralStripJetIndex χ a 1 2 := ⟨(ω, σ - a, t, K + 1), by
    change K + 1 < spectralStripMultiplicity 1 2 (σ - a)
      (multiplicity(χ ω, shift(a + (σ - a), t)))
    rw [spectralStripMultiplicity_interior (abs_lt.mp hσ), show a + (σ - a) = σ by ring]
    exact hlt⟩
  have hj := hK j (hC j)
  change K + 1 ≤ K at hj
  omega

/-- The same from the jets attached to the central line of the strip alone (real offset zero):
a uniform bound for their norms bounds the multiplicities of the zeros on the line with real
part `a`. This covers the reading of the proposition in which the ordinates are taken on that
line. -/
theorem multiplicity_bounded_of_line_upperBound (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (a : ℝ)
    (h : ∃ C : ℝ, ∀ j : SpectralStripJetIndex χ a 1 2, j.val.2.1 = 0 →
      ‖(spectralStripJet_memLp χ zero_le_one zero_le_two j).toLp (stripJet(χ, j))‖ ≤ C) :
    ∃ M : ℕ, ∀ (ω : PontryaginDual C₁) (t : ℝ), multiplicity(χ ω, shift(a, t)) ≤ M := by
  obtain ⟨C, hC⟩ := h
  obtain ⟨K, hK⟩ := order_le_of_norm_le χ a C
  refine ⟨K + 1, fun ω t ↦ ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  let j : SpectralStripJetIndex χ a 1 2 := ⟨(ω, 0, t, K + 1), by
    change K + 1 < spectralStripMultiplicity 1 2 0
      (multiplicity(χ ω, shift(a + 0, t)))
    rw [spectralStripMultiplicity_interior (by constructor <;> norm_num : (0 : ℝ) ∈ Ioo (-1) 1),
      add_zero]
    exact hlt⟩
  have hj := hK j (hC j rfl)
  change K + 1 ≤ K at hj
  omega

end UpperBound

/-! ## The rational field: Riemann zeta and Dirichlet L-functions -/

section Rational

local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "Cℚ₁" => (ideleClassNorm ℚ).ker
local notation "restrictionℚ" =>
  (⟨(ideleClassNorm ℚ).ker.subtype, continuous_subtype_val⟩ : Cℚ₁ →ₜ* Cℚ)

/-- Mathlib's Riemann zeta function is meromorphic on the plane. -/
theorem meromorphicOn_riemannZeta : MeromorphicOn riemannZeta univ := by
  simpa only [DirichletCharacter.LFunction_modOne_eq] using meromorphic_dirichletLFunction
    (1 : DirichletCharacter ℂ 1)

/-- In the right half-plane the completed L-function of the trivial character of the rational
idele class group has exactly the zeros of Riemann zeta, with their multiplicities. -/
theorem order_one_rat {s : ℂ} (hs : 0 < s.re) :
    meromorphicOrderAt (continuedCompletedHeckeL (1 : PontryaginDual Cℚ)) s =
      meromorphicOrderAt riemannZeta s :=
  (meromorphicOrderAt_finiteHeckeL_continuation (1 : PontryaginDual Cℚ) meromorphicOn_riemannZeta
    (fun z ↦ (dedekindZeta_rat_eq_riemannZeta z.2).symm.trans
      (finiteHeckeL_one_eq_dedekindZeta (K := ℚ) z).symm) hs).symm

/-- A primitive Dirichlet character has an idelic lift whose completed L-function has, in the
right half-plane, exactly the zeros of the Dirichlet L-function, with their multiplicities. -/
theorem order_dirichlet {N : ℕ} [NeZero N] {η : DirichletCharacter ℂ N} (hη : η.IsPrimitive) :
    ∃ ψ : PontryaginDual Cℚ, ∀ s : ℂ, 0 < s.re →
      meromorphicOrderAt (continuedCompletedHeckeL ψ) s =
        meromorphicOrderAt (DirichletCharacter.LFunction η) s := by
  obtain ⟨ψ, -, hL⟩ := DirichletCharacter.IsPrimitive.exists_finiteHeckeL_eq hη
  exact ⟨ψ, fun s hs ↦ (meromorphicOrderAt_finiteHeckeL_continuation ψ
    (meromorphic_dirichletLFunction η)
    (fun z ↦ by rw [DirichletCharacter.LFunction_eq_LSeries η z.2, hL z.1 z.2]) hs).symm⟩

/-- From a bound on the truncated meromorphic order to a bound on the order of vanishing. -/
theorem analyticOrderAt_le_of_toNat_le {f : ℂ → ℂ} {s : ℂ} (ha : AnalyticAt ℂ f s)
    (hfin : meromorphicOrderAt f s ≠ ⊤) {M : ℕ}
    (h : (meromorphicOrderAt f s).untop₀.toNat ≤ M) : analyticOrderAt f s ≤ M := by
  rw [ha.meromorphicOrderAt_eq] at hfin h
  cases hk : analyticOrderAt f s with
  | top => rw [hk] at hfin; exact absurd rfl hfin
  | coe k =>
    rw [hk] at h
    have hk' : k ≤ M := by simpa using h
    exact_mod_cast hk'

/-- A zero of order above one, seen by the truncated meromorphic order. -/
theorem one_lt_toNat_of_one_lt_analyticOrderAt {f : ℂ → ℂ} {s : ℂ}
    (hfin : meromorphicOrderAt f s ≠ ⊤) (h : 1 < analyticOrderAt f s) :
    1 < (meromorphicOrderAt f s).untop₀.toNat := by
  have ha : AnalyticAt ℂ f s := by
    by_contra hna
    rw [analyticOrderAt_of_not_analyticAt hna] at h
    exact absurd h (by simp)
  rw [ha.meromorphicOrderAt_eq] at hfin ⊢
  cases hk : analyticOrderAt f s with
  | top => rw [hk] at hfin; exact absurd rfl hfin
  | coe k =>
    rw [hk] at h
    have hk' : 1 < k := by exact_mod_cast h
    simpa using hk'

/-- **The target at `x = 1/2` over `ℚ` gives a height-independent bound for the multiplicities
of the zeros of the Riemann zeta function near the critical line.** -/
theorem riemannZeta_multiplicity_bounded_near_critical_line
    (χ : PontryaginDual Cℚ₁ → PontryaginDual Cℚ) (hχ : IsSpectralBasepointChoice χ)
    (h : LocallyFiniteAt χ (1 / 2)) :
    ∃ ε > (0 : ℝ), ∃ M : ℕ, ∀ s : ℂ, |s.re - 1 / 2| < ε →
      analyticOrderAt riemannZeta s ≤ M := by
  obtain ⟨U, hU, M, hM⟩ := bounded_of_locallyFiniteAt hχ h
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨min ε₀ (1 / 2), lt_min hε₀ (by norm_num), M, fun s hs ↦ ?_⟩
  have hs1 : |s.re - 1 / 2| < ε₀ := hs.trans_le (min_le_left _ _)
  have hs2 : |s.re - 1 / 2| < 1 / 2 := hs.trans_le (min_le_right _ _)
  have hpos : 0 < s.re := by linarith [(abs_lt.mp hs2).1]
  have hlt : s.re < 1 := by linarith [(abs_lt.mp hs2).2]
  have hne : s ≠ 1 := fun h ↦ by rw [h] at hlt; simp at hlt
  have hU' : s.re ∈ U := hball (by rwa [Metric.mem_ball, Real.dist_eq])
  have hb := hM 1 s.re s.im hU' hpos
  rw [Complex.re_add_im, order_one_rat hpos] at hb
  exact analyticOrderAt_le_of_toNat_le (analyticOn_riemannZeta s hne)
    (order_one_rat hpos ▸ order_ne_top (1 : PontryaginDual Cℚ) s) hb

/-- **The target over `ℚ` bounds the multiplicity of every nontrivial zero of the Riemann zeta
function by one integer.** -/
theorem riemannZeta_multiplicity_bounded
    (χ : PontryaginDual Cℚ₁ → PontryaginDual Cℚ) (hχ : IsSpectralBasepointChoice χ)
    (h : ∀ x : ℝ, LocallyFiniteAt χ x) :
    ∃ M : ℕ, ∀ s : ℂ, 0 < s.re → s ≠ 1 → analyticOrderAt riemannZeta s ≤ M := by
  obtain ⟨M, hM⟩ := bounded_of_locallyFinite hχ h
  refine ⟨M, fun s hs hne ↦ ?_⟩
  have hb := hM 1 s hs
  rw [order_one_rat hs] at hb
  exact analyticOrderAt_le_of_toNat_le (analyticOn_riemannZeta s hne)
    (order_one_rat hs ▸ order_ne_top (1 : PontryaginDual Cℚ) s) hb

/-- **The target over `ℚ` bounds by one integer the order of vanishing of every primitive
Dirichlet L-function at every point of the right half-plane**, uniformly in the character,
the conductor and the height. -/
theorem dirichlet_multiplicity_bounded
    (χ : PontryaginDual Cℚ₁ → PontryaginDual Cℚ) (hχ : IsSpectralBasepointChoice χ)
    (h : ∀ x : ℝ, LocallyFiniteAt χ x) :
    ∃ M : ℕ, ∀ (N : ℕ) [NeZero N] (η : DirichletCharacter ℂ N), η.IsPrimitive →
      ∀ s : ℂ, 0 < s.re → s ≠ 1 → analyticOrderAt (DirichletCharacter.LFunction η) s ≤ M := by
  obtain ⟨M, hM⟩ := bounded_of_locallyFinite hχ h
  refine ⟨M, fun N _ η hη s hs hne ↦ ?_⟩
  obtain ⟨ψ, hψ⟩ := order_dirichlet hη
  have hb := hM ψ s hs
  rw [hψ s hs] at hb
  have hd : DifferentiableOn ℂ (DirichletCharacter.LFunction η) {1}ᶜ := fun z hz ↦
    (DirichletCharacter.differentiableAt_LFunction η z (.inl hz)).differentiableWithinAt
  exact analyticOrderAt_le_of_toNat_le (hd.analyticAt (isOpen_compl_singleton.mem_nhds hne))
    (hψ s hs ▸ order_ne_top ψ s) hb

/-- **The target over `ℚ` puts the multiple zeros of all primitive Dirichlet L-functions, the
Riemann zeta function included, on finitely many vertical lines.** -/
theorem dirichlet_multiple_zero_lines_finite
    (χ : PontryaginDual Cℚ₁ → PontryaginDual Cℚ) (hχ : IsSpectralBasepointChoice χ)
    (h : ∀ x : ℝ, LocallyFiniteAt χ x) :
    {σ : ℝ | 0 < σ ∧ ∃ (N : ℕ) (_ : NeZero N) (η : DirichletCharacter ℂ N), η.IsPrimitive ∧
      ∃ t : ℝ, 1 < analyticOrderAt (DirichletCharacter.LFunction η) (shift(σ, t))}.Finite := by
  apply (finite_re_of_locallyFinite hχ h).subset
  rintro σ ⟨hσ, N, _, η, hη, t, hn⟩
  obtain ⟨ψ, hψ⟩ := order_dirichlet hη
  have hs : 0 < (shift(σ, t)).re := by simpa using hσ
  refine ⟨hσ, ψ, t, ?_⟩
  rw [hψ _ hs]
  exact one_lt_toNat_of_one_lt_analyticOrderAt (hψ _ hs ▸ order_ne_top ψ _) hn

/-- The same at `x = 1/2` only, for all primitive Dirichlet L-functions: a bound, uniform in
the character, for the order of vanishing near the critical line, the central point included. -/
theorem dirichlet_multiplicity_bounded_near_critical_line
    (χ : PontryaginDual Cℚ₁ → PontryaginDual Cℚ) (hχ : IsSpectralBasepointChoice χ)
    (h : LocallyFiniteAt χ (1 / 2)) :
    ∃ ε > (0 : ℝ), ∃ M : ℕ, ∀ (N : ℕ) [NeZero N] (η : DirichletCharacter ℂ N),
      η.IsPrimitive → ∀ s : ℂ, |s.re - 1 / 2| < ε →
        analyticOrderAt (DirichletCharacter.LFunction η) s ≤ M := by
  obtain ⟨U, hU, M, hM⟩ := bounded_of_locallyFiniteAt hχ h
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨min ε₀ (1 / 2), lt_min hε₀ (by norm_num), M, fun N _ η hη s hs ↦ ?_⟩
  have hs1 : |s.re - 1 / 2| < ε₀ := hs.trans_le (min_le_left _ _)
  have hs2 : |s.re - 1 / 2| < 1 / 2 := hs.trans_le (min_le_right _ _)
  have hpos : 0 < s.re := by linarith [(abs_lt.mp hs2).1]
  have hlt : s.re < 1 := by linarith [(abs_lt.mp hs2).2]
  have hne : s ≠ 1 := fun h ↦ by rw [h] at hlt; simp at hlt
  have hU' : s.re ∈ U := hball (by rwa [Metric.mem_ball, Real.dist_eq])
  obtain ⟨ψ, hψ⟩ := order_dirichlet hη
  have hb := hM ψ s.re s.im hU' hpos
  rw [Complex.re_add_im, hψ s hpos] at hb
  have hd : DifferentiableOn ℂ (DirichletCharacter.LFunction η) {1}ᶜ := fun z hz ↦
    (DirichletCharacter.differentiableAt_LFunction η z (.inl hz)).differentiableWithinAt
  exact analyticOrderAt_le_of_toNat_le (hd.analyticAt (isOpen_compl_singleton.mem_nhds hne))
    (hψ s hpos ▸ order_ne_top ψ s) hb

/-- The statement about Riemann zeta with the hypothesis written out: it is the conclusion of
the private lemma for the rational field at the real number `1/2`. -/
theorem riemannZeta_multiplicity_bounded_near_critical_line_explicit
    (χ : PontryaginDual Cℚ₁ → PontryaginDual Cℚ) (hχ : IsSpectralBasepointChoice χ)
    (h : ∃ U ∈ 𝓝 (1 / 2 : ℝ), {p : ℝ × ℕ | p.1 ∈ U ∧ 1 < p.2 ∧
      ∃ (ω : PontryaginDual Cℚ₁) (t : ℝ),
        (meromorphicOrderAt (continuedCompletedHeckeL (χ ω))
          ((p.1 : ℂ) + (t : ℂ) * Complex.I)).untop₀.toNat = p.2}.Finite) :
    ∃ ε > (0 : ℝ), ∃ M : ℕ, ∀ s : ℂ, |s.re - 1 / 2| < ε →
      analyticOrderAt riemannZeta s ≤ M :=
  riemannZeta_multiplicity_bounded_near_critical_line χ hχ h

/-! ### Over `ℚ` the target is equivalent to a statement about Dirichlet L-functions -/

/-- Every chosen base point over `ℚ` has, in the right half-plane, the zeros of a primitive
Dirichlet L-function, moved vertically. -/
theorem order_basepoint_rat {χ : PontryaginDual Cℚ₁ → PontryaginDual Cℚ}
    (hχ : IsSpectralBasepointChoice χ) (ω : PontryaginDual Cℚ₁) :
    ∃ (N : ℕ) (_ : NeZero N) (η : DirichletCharacter ℂ N), η.IsPrimitive ∧ ∃ τ : ℝ,
      ∀ σ t : ℝ, 0 < σ →
        meromorphicOrderAt (continuedCompletedHeckeL (χ ω)) (shift(σ, t)) =
          meromorphicOrderAt (DirichletCharacter.LFunction η) (shift(σ, (t - τ : ℝ))) := by
  let n : Cℚ →ₜ* ℝ≥0ˣ := ⟨ideleClassNorm ℚ, (isProperMap_ideleClassNorm ℚ).continuous⟩
  let q : IdeleGroup (𝓞 ℚ) ℚ →ₜ* Cℚ := ⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩
  let τs : ℝ≥0ˣ →ₜ* Cℚ := q.comp
    ⟨canonicalIdeleNormSection ℚ, canonicalIdeleNormSection_continuous ℚ⟩
  have hτs : Function.RightInverse τs (ideleClassNorm ℚ) :=
    canonicalIdeleNormSection_rightInverse ℚ
  let P : Cℚ →ₜ* Cℚ := ContinuousMonoidHom.id Cℚ / τs.comp n
  let θ : PontryaginDual Cℚ := (χ ω).comp P
  have hθsec : ∀ u : ℝ≥0ˣ, θ (τs u) = 1 := by
    intro u
    change χ ω (τs u / τs (ideleClassNorm ℚ (τs u))) = 1
    rw [hτs u, div_self', map_one]
  have hθres : θ.comp restrictionℚ = ω := by
    refine Eq.trans ?_ (hχ ω)
    ext g : 1
    change χ ω ((g : Cℚ) / τs (ideleClassNorm ℚ (g : Cℚ))) = χ ω (g : Cℚ)
    rw [show ideleClassNorm ℚ (g : Cℚ) = 1 from g.property, map_one, div_one]
  obtain ⟨N, hN, η, hη, hL⟩ :=
    exists_primitive_finiteHeckeL_eq_of_trivial_on_section τs hτs θ hθsec
  obtain ⟨τ, hτ⟩ := order_eq_basepoint' hχ θ
  refine ⟨N, hN, η, hη, τ, fun σ t hσ ↦ ?_⟩
  have h1 := hτ σ (t - τ) hσ
  rw [hθres, sub_add_cancel] at h1
  rw [← h1]
  exact (meromorphicOrderAt_finiteHeckeL_continuation θ (meromorphic_dirichletLFunction η)
    (fun z ↦ by rw [DirichletCharacter.LFunction_eq_LSeries η z.2, hL z.1 z.2])
    (by simpa using hσ)).symm

/-- From a bound on the order of vanishing to a bound on the truncated meromorphic order. -/
theorem toNat_le_of_analyticOrderAt_le {f : ℂ → ℂ} {s : ℂ} (ha : AnalyticAt ℂ f s) {M : ℕ}
    (h : analyticOrderAt f s ≤ M) : (meromorphicOrderAt f s).untop₀.toNat ≤ M := by
  rw [ha.meromorphicOrderAt_eq]
  cases hk : analyticOrderAt f s with
  | top => rw [hk] at h; simp at h
  | coe k =>
    rw [hk] at h
    have hk' : k ≤ M := by exact_mod_cast h
    simpa using hk'

/-- A truncated meromorphic order above one is an order of vanishing above one. -/
theorem one_lt_analyticOrderAt_of_one_lt_toNat {f : ℂ → ℂ} {s : ℂ} (ha : AnalyticAt ℂ f s)
    (h : 1 < (meromorphicOrderAt f s).untop₀.toNat) : 1 < analyticOrderAt f s := by
  rw [ha.meromorphicOrderAt_eq] at h
  cases hk : analyticOrderAt f s with
  | top => exact ENat.natCast_lt_top 1
  | coe k =>
    rw [hk] at h
    have hk' : 1 < k := by simpa using h
    exact_mod_cast hk'

/-- **Over `ℚ` the target is equivalent to a statement about Dirichlet L-functions alone:** one
integer bounds the order of vanishing of all primitive Dirichlet L-functions in the right
half-plane, and their multiple zeros lie on finitely many vertical lines. -/
theorem rat_locallyFinite_iff_dirichlet
    (χ : PontryaginDual Cℚ₁ → PontryaginDual Cℚ) (hχ : IsSpectralBasepointChoice χ) :
    (∀ x : ℝ, LocallyFiniteAt χ x) ↔
      (∃ M : ℕ, ∀ (N : ℕ) [NeZero N] (η : DirichletCharacter ℂ N), η.IsPrimitive →
        ∀ s : ℂ, 0 < s.re → s ≠ 1 → analyticOrderAt (DirichletCharacter.LFunction η) s ≤ M) ∧
      {σ : ℝ | 0 < σ ∧ ∃ (N : ℕ) (_ : NeZero N) (η : DirichletCharacter ℂ N), η.IsPrimitive ∧
        ∃ t : ℝ, shift(σ, t) ≠ 1 ∧
          1 < analyticOrderAt (DirichletCharacter.LFunction η) (shift(σ, t))}.Finite := by
  refine ⟨fun h ↦ ⟨dirichlet_multiplicity_bounded χ hχ h,
    (dirichlet_multiple_zero_lines_finite χ hχ h).subset ?_⟩, ?_⟩
  · rintro σ ⟨hσ, N, hN, η, hη, t, -, hn⟩
    exact ⟨hσ, N, hN, η, hη, t, hn⟩
  rintro ⟨⟨M, hM⟩, hfin⟩
  -- a zero of a base point is a zero of a primitive Dirichlet L-function off the point one
  have key (ω : PontryaginDual Cℚ₁) (σ t : ℝ)
      (hpos : 0 < multiplicity(χ ω, shift(σ, t))) :
      0 < σ ∧ ∃ (N : ℕ) (_ : NeZero N) (η : DirichletCharacter ℂ N), η.IsPrimitive ∧
        ∃ t' : ℝ, AnalyticAt ℂ (DirichletCharacter.LFunction η) (shift(σ, t')) ∧
          shift(σ, t') ≠ 1 ∧
          multiplicity(χ ω, shift(σ, t)) =
            (meromorphicOrderAt (DirichletCharacter.LFunction η) (shift(σ, t'))).untop₀.toNat := by
    have hre : (shift(σ, t)).re = σ := by simp
    have hstrip : σ ∈ Ioo (0 : ℝ) 1 := by
      by_contra hout
      have h0 := multiplicity_eq_zero_outside_open (χ ω) (shift(σ, t)) (by rwa [hre])
      omega
    obtain ⟨N, hN, η, hη, τ, hτ⟩ := order_basepoint_rat hχ ω
    have hne : shift(σ, (t - τ : ℝ)) ≠ 1 := by
      intro h1
      have := congrArg Complex.re h1
      simp at this
      linarith [hstrip.2]
    have hd : DifferentiableOn ℂ (DirichletCharacter.LFunction η) {1}ᶜ := fun z hz ↦
      (DirichletCharacter.differentiableAt_LFunction η z (.inl hz)).differentiableWithinAt
    exact ⟨hstrip.1, N, hN, η, hη, t - τ,
      hd.analyticAt (isOpen_compl_singleton.mem_nhds hne), hne, by rw [hτ σ t hstrip.1]⟩
  apply (locallyFinite_iff χ).mpr
  constructor
  · refine ⟨M, fun ω σ t ↦ ?_⟩
    rcases Nat.eq_zero_or_pos (multiplicity(χ ω, shift(σ, t))) with h0 | hpos
    · rw [h0]
      exact Nat.zero_le _
    · obtain ⟨hσ, N, hN, η, hη, t', ha, hne, heq⟩ := key ω σ t hpos
      rw [heq]
      exact toNat_le_of_analyticOrderAt_le ha (hM N η hη _ (by simpa using hσ) hne)
  · apply hfin.subset
    rintro σ ⟨ω, t, hn⟩
    obtain ⟨hσ, N, hN, η, hη, t', ha, hne, heq⟩ := key ω σ t (by omega)
    rw [heq] at hn
    exact ⟨hσ, N, hN, η, hη, t', hne, one_lt_analyticOrderAt_of_one_lt_toNat ha hn⟩

/-- **Over `ℚ` the target follows from the simplicity of the zeros of the primitive Dirichlet
L-functions in the right half-plane**, a standard conjecture. With
`riemannZeta_multiplicity_bounded` this places the target over `ℚ` between two open
statements. -/
theorem rat_locallyFinite_of_simple_zeros
    (χ : PontryaginDual Cℚ₁ → PontryaginDual Cℚ) (hχ : IsSpectralBasepointChoice χ)
    (hsimple : ∀ (N : ℕ) [NeZero N] (η : DirichletCharacter ℂ N), η.IsPrimitive →
      ∀ s : ℂ, 0 < s.re → s ≠ 1 → analyticOrderAt (DirichletCharacter.LFunction η) s ≤ 1) :
    ∀ x : ℝ, LocallyFiniteAt χ x := by
  apply (rat_locallyFinite_iff_dirichlet χ hχ).mpr
  refine ⟨⟨1, fun N _ η hη s hs hne ↦ by exact_mod_cast hsimple N η hη s hs hne⟩, ?_⟩
  refine (Set.finite_empty (α := ℝ)).subset ?_
  rintro σ ⟨hσ, N, hN, η, hη, t, hne, hn⟩
  have h1 := hsimple N η hη (shift(σ, t)) (by simpa using hσ) hne
  exact absurd (lt_of_lt_of_le hn h1) (lt_irrefl _)

/-- **The strip estimate of Proposition 10.2.2.2 over `ℚ`, at Sobolev exponent 2 and half-width
1 alone, already bounds the multiplicity of every nontrivial zero of Riemann zeta.** The
hypothesis is the conclusion of the public theorem `spectralStripJet_order_and_margin`. -/
theorem riemannZeta_multiplicity_bounded_of_strip_estimate
    (χ : PontryaginDual Cℚ₁ → PontryaginDual Cℚ) (hχ : IsSpectralBasepointChoice χ)
    (h : ∀ a : ℝ, ∃ (K : ℕ) (δ : ℝ), 0 < δ ∧ ∀ j : SpectralStripJetIndex χ a 1 2,
      j.val.2.2.2 ≤ K ∧ ((2 - 1) / 2 ≤ (j.val.2.2.2 : ℝ) → |j.val.2.1| ≤ 1 - δ)) :
    ∃ M : ℕ, ∀ s : ℂ, 0 < s.re → s ≠ 1 → analyticOrderAt riemannZeta s ≤ M :=
  riemannZeta_multiplicity_bounded χ hχ (locallyFiniteAt_of_unit_strips χ h)

/-! ### What the library asserts as long as the `sorry` stands -/

/-- With the private lemma as it stands (`sorryAx`), the library asserts a height-independent
bound for the multiplicities of the nontrivial zeros of the Riemann zeta function. -/
theorem riemannZeta_multiplicity_bounded_from_target :
    ∃ M : ℕ, ∀ s : ℂ, 0 < s.re → s ≠ 1 → analyticOrderAt riemannZeta s ≤ M := by
  obtain ⟨χ, hχ⟩ := exists_spectralBasepointChoice ℚ
  exact riemannZeta_multiplicity_bounded χ hχ (locallyFiniteAt_of_target χ hχ)

/-- The same for all primitive Dirichlet L-functions at once. -/
theorem dirichlet_multiplicity_bounded_from_target :
    ∃ M : ℕ, ∀ (N : ℕ) [NeZero N] (η : DirichletCharacter ℂ N), η.IsPrimitive →
      ∀ s : ℂ, 0 < s.re → s ≠ 1 → analyticOrderAt (DirichletCharacter.LFunction η) s ≤ M := by
  obtain ⟨χ, hχ⟩ := exists_spectralBasepointChoice ℚ
  exact dirichlet_multiplicity_bounded χ hχ (locallyFiniteAt_of_target χ hχ)

/-- The same through the public theorem `spectralStripJet_order_and_margin`, which rests on the
private lemma. -/
theorem riemannZeta_multiplicity_bounded_from_gap :
    ∃ M : ℕ, ∀ s : ℂ, 0 < s.re → s ≠ 1 → analyticOrderAt riemannZeta s ≤ M := by
  obtain ⟨χ, hχ⟩ := exists_spectralBasepointChoice ℚ
  exact riemannZeta_multiplicity_bounded_of_strip_estimate χ hχ fun a ↦
    spectralStripJet_order_and_margin (a := a) χ hχ zero_le_one one_lt_two

end Rational

/-! ## One instance of the proposition over `ℚ` bounds the multiplicities of the zeta zeros -/

section RationalUpperBound

open MeasureTheory

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "Cℚ₁" => (ideleClassNorm ℚ).ker
local notation "stripJet(" χ ", " j ")" =>
  spectralZeroJet (χ (j).val.1) (j).val.2.1 (j).val.2.2.1 (j).val.2.2.2

/-- **A uniform bound for the norms of the strip jets over `ℚ`, for the single strip with
center `1/2`, half-width `1` and Sobolev exponent `2`, bounds the multiplicity of every
nontrivial zero of the Riemann zeta function.** The hypothesis is the conclusion of
`spectralStripJet_upperBound` (Proposition 10.2.2.2) in that one instance, without the
positivity of the constant. -/
theorem riemannZeta_multiplicity_bounded_of_upperBound
    (χ : PontryaginDual Cℚ₁ → PontryaginDual Cℚ) (hχ : IsSpectralBasepointChoice χ)
    (h : ∃ C : ℝ, ∀ j : SpectralStripJetIndex χ (1 / 2) 1 2,
      ‖(spectralStripJet_memLp χ zero_le_one zero_le_two j).toLp (stripJet(χ, j))‖ ≤ C) :
    ∃ M : ℕ, ∀ s : ℂ, 0 < s.re → s ≠ 1 → analyticOrderAt riemannZeta s ≤ M := by
  obtain ⟨M, hM⟩ := multiplicity_bounded_of_upperBound χ (1 / 2) h
  obtain ⟨τ, hτ⟩ := order_eq_basepoint' hχ (1 : PontryaginDual Cℚ)
  refine ⟨M, fun s hs hne ↦ ?_⟩
  by_cases hlt : s.re < 1
  · have hb := hM ((1 : PontryaginDual Cℚ).comp
      (⟨(ideleClassNorm ℚ).ker.subtype, continuous_subtype_val⟩ : Cℚ₁ →ₜ* Cℚ))
      s.re (s.im + τ) (by rw [abs_lt]; constructor <;> linarith)
    rw [← hτ s.re s.im hs, Complex.re_add_im, order_one_rat hs] at hb
    exact analyticOrderAt_le_of_toNat_le (analyticOn_riemannZeta s hne)
      (order_one_rat hs ▸ order_ne_top (1 : PontryaginDual Cℚ) s) hb
  · have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re (not_lt.mp hlt)
    rw [(analyticOn_riemannZeta s hne).analyticOrderAt_eq_zero.mpr hz]
    exact zero_le

/-- **A uniform bound for the norms of the jets on the central line alone, over `ℚ` with center
`1/2`, bounds the multiplicities of the zeros of Riemann zeta on the critical line.** -/
theorem riemannZeta_critical_line_multiplicity_bounded_of_line_upperBound
    (χ : PontryaginDual Cℚ₁ → PontryaginDual Cℚ) (hχ : IsSpectralBasepointChoice χ)
    (h : ∃ C : ℝ, ∀ j : SpectralStripJetIndex χ (1 / 2) 1 2, j.val.2.1 = 0 →
      ‖(spectralStripJet_memLp χ zero_le_one zero_le_two j).toLp (stripJet(χ, j))‖ ≤ C) :
    ∃ M : ℕ, ∀ t : ℝ, analyticOrderAt riemannZeta (1 / 2 + (t : ℂ) * Complex.I) ≤ M := by
  obtain ⟨M, hM⟩ := multiplicity_bounded_of_line_upperBound χ (1 / 2) h
  obtain ⟨τ, hτ⟩ := order_eq_basepoint' hχ (1 : PontryaginDual Cℚ)
  refine ⟨M, fun t ↦ ?_⟩
  have he : (1 / 2 + (t : ℂ) * Complex.I) = (((1 / 2 : ℝ) : ℝ) : ℂ) + (t : ℂ) * Complex.I := by
    push_cast
    rfl
  rw [he]
  have hs : 0 < ((((1 / 2 : ℝ) : ℝ) : ℂ) + (t : ℂ) * Complex.I).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
    norm_num
  have hne : (((1 / 2 : ℝ) : ℝ) : ℂ) + (t : ℂ) * Complex.I ≠ 1 := by
    intro h1
    have h2 := congrArg Complex.re h1
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.one_re] at h2
    norm_num at h2
  have hb := hM ((1 : PontryaginDual Cℚ).comp
    (⟨(ideleClassNorm ℚ).ker.subtype, continuous_subtype_val⟩ : Cℚ₁ →ₜ* Cℚ)) (t + τ)
  rw [← hτ (1 / 2) t (by norm_num), order_one_rat hs] at hb
  exact analyticOrderAt_le_of_toNat_le (analyticOn_riemannZeta _ hne)
    (order_one_rat hs ▸ order_ne_top (1 : PontryaginDual Cℚ) _) hb

/-- Through the public theorem `spectralStripJet_upperBound` (Proposition 10.2.2.2), which
rests on the private lemma. -/
theorem riemannZeta_multiplicity_bounded_from_proposition :
    ∃ M : ℕ, ∀ s : ℂ, 0 < s.re → s ≠ 1 → analyticOrderAt riemannZeta s ≤ M := by
  obtain ⟨χ, hχ⟩ := exists_spectralBasepointChoice ℚ
  obtain ⟨C, -, hC⟩ := spectralStripJet_upperBound (a := 1 / 2) χ hχ zero_le_one one_lt_two
  exact riemannZeta_multiplicity_bounded_of_upperBound χ hχ ⟨C, hC⟩

/-- Through the public theorem `spectralStripMarkushevichBasis_normalized`
(Corollary 10.2.2.3), which rests on the private lemma. -/
theorem riemannZeta_multiplicity_bounded_from_corollary :
    ∃ M : ℕ, ∀ s : ℂ, 0 < s.re → s ≠ 1 → analyticOrderAt riemannZeta s ≤ M := by
  obtain ⟨χ, hχ⟩ := exists_spectralBasepointChoice ℚ
  obtain ⟨x, Λ, -, hD, ⟨C, hC⟩, -⟩ :=
    spectralStripMarkushevichBasis_normalized (a := 1 / 2) χ hχ zero_le_one one_lt_two
  exact riemannZeta_multiplicity_bounded_of_upperBound χ hχ ⟨C, fun j ↦ hD j ▸ hC j⟩

end RationalUpperBound

/-! ## A field with non-abelian Galois group: a zero-free strip -/

section NonAbelian

local notation "ζChar(" E ")" => (1 : PontryaginDual (IdeleClassGroup (𝓞 E) E))
local notation "ord(" E ", " z ")" =>
  (meromorphicOrderAt (continuedCompletedHeckeL (1 : PontryaginDual (IdeleClassGroup (𝓞 E) E)))
    z).untop₀.toNat

/-- A finite set of reals below one stays a fixed distance below one. -/
theorem exists_margin_of_finite {S : Set ℝ} (hS : S.Finite) (h1 : ∀ σ ∈ S, σ < 1) :
    ∃ δ > (0 : ℝ), δ ≤ 1 ∧ ∀ σ ∈ S, σ ≤ 1 - δ := by
  obtain ⟨m, hm, hmax⟩ := Set.exists_max_image (insert 0 S) id (hS.insert 0)
    (insert_nonempty _ _)
  have hm1 : m < 1 := by
    rcases hm with rfl | hm
    · exact zero_lt_one
    · exact h1 m hm
  have hm0 : (0 : ℝ) ≤ m := hmax 0 (mem_insert _ _)
  exact ⟨1 - m, by linarith, by linarith, fun σ hσ ↦ by
    have := hmax σ (mem_insert_of_mem _ hσ)
    simp only [id] at this
    linarith⟩

/-- Every meromorphic continuation of a Dedekind zeta function has, in the right half-plane,
the zeros of the completed L-function of the trivial character. -/
theorem order_dedekind (K : Type) [Field K] [NumberField K] {f : ℂ → ℂ}
    (hf : MeromorphicOn f univ) (h : ∀ s : ℂ, 1 < s.re → f s = dedekindZeta K s) {s : ℂ}
    (hs : 0 < s.re) :
    meromorphicOrderAt f s = meromorphicOrderAt (continuedCompletedHeckeL ζChar(K)) s :=
  meromorphicOrderAt_finiteHeckeL_continuation ζChar(K) hf
    (fun z ↦ (h z z.2).trans (finiteHeckeL_one_eq_dedekindZeta (K := K) z).symm) hs

/-- If the zeta function of `L` vanishes doubly wherever the zeta function of `K` vanishes to
higher order than Riemann zeta, the conclusion of the target for `L` at `x = 1` alone gives a
strip to the left of one in which the quotient of the zeta function of `K` by Riemann zeta has
no zero. -/
theorem zero_free_strip_of_orderRelation (L K : Type) [Field L] [NumberField L] [Field K]
    [NumberField K]
    (hrel : ∀ z : ℂ, 0 < z.re → z.re < 1 → 2 * ord(K, z) ≤ ord(L, z) + 2 * ord(ℚ, z))
    (χ : PontryaginDual (ideleClassNorm L).ker → PontryaginDual (IdeleClassGroup (𝓞 L) L))
    (hχ : IsSpectralBasepointChoice χ) (h : LocallyFiniteAt χ 1) :
    ∃ δ > (0 : ℝ), ∀ s : ℂ, 1 - δ < s.re → s.re < 1 → ord(K, s) ≤ ord(ℚ, s) := by
  obtain ⟨U, hU, hfin⟩ := finite_re_of_locallyFiniteAt hχ h
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  obtain ⟨δ₀, hδ₀, hδ₀1, hmargin⟩ := exists_margin_of_finite (hfin.inter_of_left (Iio 1))
    (fun σ hσ ↦ hσ.2)
  refine ⟨min δ₀ ε, lt_min hδ₀ hε, fun s hs1 hs2 ↦ ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  have hpos : 0 < s.re := by linarith [min_le_left δ₀ ε]
  have hmult : 1 < ord(L, s) := by
    have := hrel s hpos hs2
    omega
  have hsU : s.re ∈ U := hball (by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [min_le_right δ₀ ε])
  have hmem := hmargin s.re ⟨⟨hsU, hpos, ζChar(L), s.im, by rwa [Complex.re_add_im]⟩, hs2⟩
  linarith [min_le_left δ₀ ε]

/-- The polynomial `X³ − 2`. -/
abbrev cubicPoly : Polynomial ℚ := Polynomial.X ^ 3 - Polynomial.C 2

theorem cubicPoly_irreducible : Irreducible cubicPoly := by
  apply irreducible_X_pow_sub_C_of_prime (by decide : Nat.Prime 3)
  intro q hq
  have h := congrArg (padicValRat 2) hq
  rw [padicValRat.pow, show padicValRat 2 2 = 1 from padicValRat.self (by decide : 1 < 2)] at h
  norm_num at h
  omega

instance cubicPoly_fact : Fact (Irreducible cubicPoly) := ⟨cubicPoly_irreducible⟩

/-- The cubic field `ℚ(∛2)`. -/
abbrev cubicField : Type := AdjoinRoot cubicPoly

/-- The splitting field of `X³ − 2`: degree six over `ℚ`, Galois group `S₃`. -/
abbrev cubicClosure : Type := cubicPoly.SplittingField

instance cubicClosure_numberField : NumberField cubicClosure := ⟨⟩

/-- The identity `ζ_L ζ² = ζ_k ζ_K²` of the library, read on the orders of zeros in the open
strip: where `ζ_K` vanishes to higher order than `ζ`, the function `ζ_L` vanishes doubly. -/
theorem cubic_orderRelation (z : ℂ) (h₀ : 0 < z.re) (h₁ : z.re < 1) :
    2 * ord(cubicField, z) ≤ ord(cubicClosure, z) + 2 * ord(ℚ, z) := by
  classical
  let P : Polynomial ℚ := Polynomial.X ^ 3 - Polynomial.C 2
  let Q : Polynomial ℚ := Polynomial.X ^ 2 + Polynomial.C 3
  have hirr : Irreducible P := cubicPoly_irreducible
  let K := AdjoinRoot P
  let L := P.SplittingField
  let k := Q.SplittingField
  have : IsGalois ℚ L := IsGalois.of_separable_splitting_field hirr.separable
  have : NumberField k := ⟨⟩
  let b := AdjoinRoot.powerBasis (Polynomial.X_pow_sub_C_ne_zero (by decide : 0 < 3) (2 : ℚ))
  have hd : b.dim = 3 := by rw [AdjoinRoot.powerBasis_dim, Polynomial.natDegree_X_pow_sub_C]
  have hG := spectralLineJet_memLp_false_cubicGalois P rfl hirr
  obtain ⟨ιK, ιk, hk⟩ := spectralLineJet_memLp_false_subfields P rfl hirr
  have hprimes := spectralLineJet_memLp_false_primeCounts L k K hG ιk hk ιK (b.finrank.trans hd)
  have hrel := spectralLineJet_memLp_false_orderRelation L k K
    (spectralLineJet_memLp_false_zetaRelation L k K hprimes) z h₀ h₁
  change 2 * ord(K, z) ≤ ord(L, z) + 2 * ord(ℚ, z)
  omega

/-- **The target at `x = 1` for the splitting field of `X³ − 2` gives a zero-free strip.**
For some `δ > 0`, every zero of the Dedekind zeta function of `ℚ(∛2)` with `1 − δ < Re s < 1`
is a zero of Riemann zeta of at least the same order: the quotient, which is the Artin
L-function of the two-dimensional representation of `S₃`, has no zero in that strip. -/
theorem cubic_zero_free_strip
    (χ : PontryaginDual (ideleClassNorm cubicClosure).ker →
      PontryaginDual (IdeleClassGroup (𝓞 cubicClosure) cubicClosure))
    (hχ : IsSpectralBasepointChoice χ) (h : LocallyFiniteAt χ 1) :
    ∃ δ > (0 : ℝ), ∀ f : ℂ → ℂ, MeromorphicOn f univ →
      (∀ s : ℂ, 1 < s.re → f s = dedekindZeta cubicField s) →
      ∀ s : ℂ, 1 - δ < s.re → s.re < 1 →
        meromorphicOrderAt f s ≤ meromorphicOrderAt riemannZeta s := by
  obtain ⟨δ, hδ, hstrip⟩ := zero_free_strip_of_orderRelation cubicClosure cubicField
    cubic_orderRelation χ hχ h
  refine ⟨min δ 1, lt_min hδ one_pos, fun f hf hfζ s hs1 hs2 ↦ ?_⟩
  have hpos : 0 < s.re := by linarith [min_le_right δ 1]
  have hle := hstrip s (by linarith [min_le_left δ 1]) hs2
  rw [order_dedekind cubicField hf hfζ hpos, ← order_one_rat hpos,
    spectralLineJet_memLp_false_stripOrder cubicField s hpos hs2,
    spectralLineJet_memLp_false_stripOrder ℚ s hpos hs2]
  exact_mod_cast hle

/-- With the private lemma as it stands (`sorryAx`), the library asserts this zero-free strip. -/
theorem cubic_zero_free_strip_from_target :
    ∃ δ > (0 : ℝ), ∀ f : ℂ → ℂ, MeromorphicOn f univ →
      (∀ s : ℂ, 1 < s.re → f s = dedekindZeta cubicField s) →
      ∀ s : ℂ, 1 - δ < s.re → s.re < 1 →
        meromorphicOrderAt f s ≤ meromorphicOrderAt riemannZeta s := by
  obtain ⟨χ, hχ⟩ := exists_spectralBasepointChoice cubicClosure
  exact cubic_zero_free_strip χ hχ (locallyFiniteAt_of_target χ hχ 1)

end NonAbelian

end RiemannMasullo.Gap7220

#print axioms RiemannMasullo.Gap7220.order_of_normTwist
#print axioms RiemannMasullo.Gap7220.order_eq_basepoint
#print axioms RiemannMasullo.Gap7220.locallyFinite_iff
#print axioms RiemannMasullo.Gap7220.bounded_of_locallyFinite
#print axioms RiemannMasullo.Gap7220.finite_re_of_locallyFinite
#print axioms RiemannMasullo.Gap7220.riemannZeta_multiplicity_bounded_near_critical_line
#print axioms RiemannMasullo.Gap7220.riemannZeta_multiplicity_bounded
#print axioms RiemannMasullo.Gap7220.dirichlet_multiplicity_bounded
#print axioms RiemannMasullo.Gap7220.dirichlet_multiple_zero_lines_finite
#print axioms RiemannMasullo.Gap7220.locallyFiniteAt_of_target
#print axioms RiemannMasullo.Gap7220.riemannZeta_multiplicity_bounded_from_target
#print axioms RiemannMasullo.Gap7220.dirichlet_multiplicity_bounded_from_target
#print axioms RiemannMasullo.Gap7220.zero_free_strip_of_orderRelation
#print axioms RiemannMasullo.Gap7220.cubic_orderRelation
#print axioms RiemannMasullo.Gap7220.cubic_zero_free_strip
#print axioms RiemannMasullo.Gap7220.cubic_zero_free_strip_from_target
#print axioms RiemannMasullo.Gap7220.dirichlet_multiplicity_bounded_near_critical_line
#print axioms RiemannMasullo.Gap7220.riemannZeta_multiplicity_bounded_near_critical_line_explicit
#print axioms RiemannMasullo.Gap7220.order_basepoint_rat
#print axioms RiemannMasullo.Gap7220.rat_locallyFinite_iff_dirichlet
#print axioms RiemannMasullo.Gap7220.locallyFiniteAt_of_unit_strips
#print axioms RiemannMasullo.Gap7220.riemannZeta_multiplicity_bounded_of_strip_estimate
#print axioms RiemannMasullo.Gap7220.riemannZeta_multiplicity_bounded_from_gap
#print axioms RiemannMasullo.Gap7220.order_reflect
#print axioms RiemannMasullo.Gap7220.multiplicity_eq_zero_outside_open
#print axioms RiemannMasullo.Gap7220.order_le_of_norm_le
#print axioms RiemannMasullo.Gap7220.multiplicity_bounded_of_line_upperBound
#print axioms RiemannMasullo.Gap7220.riemannZeta_critical_line_multiplicity_bounded_of_line_upperBound
#print axioms RiemannMasullo.Gap7220.multiplicity_bounded_of_upperBound
#print axioms RiemannMasullo.Gap7220.riemannZeta_multiplicity_bounded_of_upperBound
#print axioms RiemannMasullo.Gap7220.riemannZeta_multiplicity_bounded_from_proposition
#print axioms RiemannMasullo.Gap7220.riemannZeta_multiplicity_bounded_from_corollary
#print axioms RiemannMasullo.Gap7220.rat_locallyFinite_of_simple_zeros
#print axioms RiemannMasullo.Gap7220.locallyFinite_iff_all_characters
#print axioms RiemannMasullo.Gap7220.locallyFinite_iff_bounded_of_GRH
