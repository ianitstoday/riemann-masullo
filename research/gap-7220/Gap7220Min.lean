module
import all RiemannMasullo.Ch10_TraceSpectral.Sec2
import all RiemannMasullo.Ch03_IdelicZeta.Sec2
import RiemannMasullo.Ch13_ZerosHecke.Targets

/-! The conclusion of `spectralStripJet_order_and_margin_locally_finite_multiple_zeros` for the
rational field at the real number 1/2 bounds the multiplicities of the zeros of the Riemann zeta
function near the critical line. Scratch file, checked with `lake lean` at commit 5b158be; the
`import all` lines are for this file only. An excerpt of `.agent/Gap7220.lean`. -/

noncomputable section

open Filter Function NumberField Set
open scoped Topology NNReal NumberField.AdeleRing

namespace RiemannMasullo.Gap7220Min

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
local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "Cℚ₁" => (ideleClassNorm ℚ).ker

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

/-- **The conclusion of the private lemma over `ℚ` at `x = 1/2` gives a height-independent bound
for the multiplicities of the zeros of the Riemann zeta function near the critical line.** -/
theorem riemannZeta_multiplicity_bounded_near_critical_line
    (χ : PontryaginDual Cℚ₁ → PontryaginDual Cℚ) (hχ : IsSpectralBasepointChoice χ)
    (h : ∃ U ∈ 𝓝 (1 / 2 : ℝ), {p : ℝ × ℕ | p.1 ∈ U ∧ 1 < p.2 ∧
      ∃ (ω : PontryaginDual Cℚ₁) (t : ℝ),
        (meromorphicOrderAt (continuedCompletedHeckeL (χ ω))
          ((p.1 : ℂ) + (t : ℂ) * Complex.I)).untop₀.toNat = p.2}.Finite) :
    ∃ ε > (0 : ℝ), ∃ M : ℕ, ∀ s : ℂ, |s.re - 1 / 2| < ε →
      analyticOrderAt riemannZeta s ≤ M := by
  obtain ⟨U, hU, hfin⟩ := h
  obtain ⟨K, hK⟩ := (hfin.image Prod.snd).bddAbove
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.mem_nhds_iff.mp hU
  obtain ⟨τ, hτ⟩ := order_eq_basepoint' hχ (1 : PontryaginDual Cℚ)
  refine ⟨min ε₀ (1 / 2), lt_min hε₀ (by norm_num), max K 1, fun s hs ↦ ?_⟩
  have hs1 : |s.re - 1 / 2| < ε₀ := hs.trans_le (min_le_left _ _)
  have hs2 : |s.re - 1 / 2| < 1 / 2 := hs.trans_le (min_le_right _ _)
  have hpos : 0 < s.re := by linarith [(abs_lt.mp hs2).1]
  have hlt : s.re < 1 := by linarith [(abs_lt.mp hs2).2]
  have hne : s ≠ 1 := fun h ↦ by rw [h] at hlt; simp at hlt
  have hU' : s.re ∈ U := hball (by rwa [Metric.mem_ball, Real.dist_eq])
  have hb : multiplicity((1 : PontryaginDual Cℚ), shift(s.re, s.im)) ≤ max K 1 := by
    rw [hτ s.re s.im hpos]
    by_cases hn : 1 < multiplicity(χ ((1 : PontryaginDual Cℚ).comp
        (⟨(ideleClassNorm ℚ).ker.subtype, continuous_subtype_val⟩ : Cℚ₁ →ₜ* Cℚ)),
        shift(s.re, (s.im + τ : ℝ)))
    · exact (hK ⟨(s.re, _), ⟨hU', hn, _, s.im + τ, rfl⟩, rfl⟩).trans (le_max_left _ _)
    · exact (not_lt.mp hn).trans (le_max_right _ _)
  rw [Complex.re_add_im, order_one_rat hpos] at hb
  exact analyticOrderAt_le_of_toNat_le (analyticOn_riemannZeta s hne)
    (order_one_rat hpos ▸ order_ne_top (1 : PontryaginDual Cℚ) s) hb

/-- With the private lemma as it stands, the library asserts this bound outright. -/
theorem riemannZeta_multiplicity_bounded_near_critical_line_from_target :
    ∃ ε > (0 : ℝ), ∃ M : ℕ, ∀ s : ℂ, |s.re - 1 / 2| < ε →
      analyticOrderAt riemannZeta s ≤ M := by
  obtain ⟨χ, hχ⟩ := exists_spectralBasepointChoice ℚ
  exact riemannZeta_multiplicity_bounded_near_critical_line χ hχ
    (spectralStripJet_order_and_margin_locally_finite_multiple_zeros χ hχ (1 / 2))

end RiemannMasullo.Gap7220Min

#print axioms RiemannMasullo.Gap7220Min.riemannZeta_multiplicity_bounded_near_critical_line
#print axioms RiemannMasullo.Gap7220Min.riemannZeta_multiplicity_bounded_near_critical_line_from_target
