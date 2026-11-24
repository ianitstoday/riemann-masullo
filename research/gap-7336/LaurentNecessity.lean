module

public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec2

import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.StrongBidual
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.SeparatingDual
public import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec6
import RiemannMasullo.Ch03_IdelicZeta.Sec4
import RiemannMasullo.Ch02_AdelicTheta.Sec3
import RiemannMasullo.Ch05_ThetaZSpaces.Sec2b
import RiemannMasullo.Ch06_LocalGlobal.Sec3

import RiemannMasullo.AppC_LCTVS.Sec1
import all RiemannMasullo.Ch03_IdelicZeta.Sec3
import all RiemannMasullo.Ch05_ThetaZSpaces.Sec1
public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec3a
import all RiemannMasullo.Ch07_SchauderBasesZeta.Sec3a


@[expose] public noncomputable section

open Asymptotics Filter Function IsDedekindDomain NumberField Set Topology
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false
set_option maxHeartbeats 600000
set_option Elab.async false

variable {F : Type*} [Field F] [NumberField F]
variable {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "Vℚ" => HeightOneSpectrum (𝓞 ℚ)
local notation "Jₛ" => SIdeleQuotient F S
local notation "mₛ" => sIdeleQuotientNorm F S
local notation "J₁" => (mₛ).ker
local notation "Xₛ" => QuasiCharacter Jₛ
local notation "ℬₛ" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "twistₛ" => quasiCharacterNormTwist (G := Jₛ) mₛ
  (isProperMap_sIdeleQuotientNorm F S).continuous
local notation "dualₛ" => dualQuasiCharacter (G := Jₛ) mₛ
  (isProperMap_sIdeleQuotientNorm F S).continuous
local notation "circleToComplex" => (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ)
local notation "chart(" χ ")" => twistₛ ((circleToComplex).comp (χ))
local notation "onComponent(" c ", " ω ")" =>
  (normOneRestriction mₛ c = (circleToComplex).comp ω)
local notation "Θₛ(" ω ")" => SLocalHomogeneousThetaSpace F S ω
local notation "Kₛ(" ω ")" => LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap F S ω)
local notation "PV(" places ", " hT ", " ω ")" =>
  (sLocalHomogeneousThetaPrincipalValue (F := F) (S := S) (T := places) hT ω).range
local notation "PicTrivial" => Subsingleton (CommRing.Pic ((S : Set V).integer F))

local notation "I(" T ", " ω ")" => SLocalOrbitalIndex (F := F) (S := S) T ω
local notation "Sₚ(" p ")" => sLocalPrimaryPlaces (F := F) S p
local notation "hₚ(" p ")" => sLocalPrimaryPlaces_subset (F := F) S p
local notation "Rₚ(" p ", " ω ")" => sLocalPrimaryOrbitalSubmodule (F := F) (S := S) p ω
local notation "Q(" p ", " ω ")" => SLocalPrimaryOrbitalQuotient (F := F) (S := S) p ω
local notation "π(" p ", " ω ")" => (Rₚ(p, ω)).mkQ
local notation "period(" v ")" => (2 * Real.pi / Real.log ((v : S).val.asIdeal.absNorm : ℝ))
local notation "lattice(" χ ", " v ", " t ", " n ")" =>
  chart(χ) ((((n : ℝ) * period(v) - t : ℝ) : ℂ) * Complex.I)
local notation "phase(" χ ", " v ", " u ", " t ")" =>
  (t ∈ Ico 0 period(v) ∧
    sLocalFiniteRestriction v (chart(χ) (-(t : ℂ) * Complex.I)) u = 1)
local notation "uniformizerNorm(" v ", " u ")" =>
  (‖(↑(u) : (v : S).val.adicCompletion F)‖ = ((v : S).val.asIdeal.absNorm : ℝ)⁻¹)
local notation "Idx(" p ", " ω ")" => I(Sₚ(p), ω)
local notation "rhoCoeff(" c ", " r ")" =>
  complexResidue (fun z : ℂ ↦ sLocalRhoFactor (twistₛ (c) z) *
    z ^ ((sLocalRhoPoleOrder (c) : ℤ) - ((r : ℕ) : ℤ) - 1)) 0

local notation "fourierZeta(" c ")" =>
  (fun (f : ℬₛ) (z : ℂ) ↦ sLocalIdelicZFunction (sAdeleSchwartzFourier f)
    (dualₛ (twistₛ c z)))

section LaurentNecessity

/-- A theta class that is polar-biorthogonal at the first two coordinates of a center
has first Fourier jet minus the Laurent ratio divided by the leading coefficient. -/
theorem sLocalPolarTerm_fourierJet {T : Finset V} {ω : PontryaginDual J₁}
    (i i' : I(T, ω)) (hi : i.val.2 = 0) (hc : i'.val.1 = i.val.1) (hi' : i'.val.2 = 1)
    (y : Θₛ(ω)) (h0 : sLocalOrbitalPrincipalPart i y = 1)
    (h1 : sLocalOrbitalPrincipalPart i' y = 0) :
    sLocalOrbitalFourierJet i y = (rhoCoeff(i.val.1, 0))⁻¹ ∧
    sLocalOrbitalFourierJet i' y = -(rhoCoeff(i.val.1, 1) / rhoCoeff(i.val.1, 0) ^ 2) := by
  obtain ⟨f, rfl⟩ := (Kₛ(ω)).mkQ_surjective y
  have hne := (orbitalPolar_leading i f).1
  have r0 := orbitalPolar_row i f
  have r1 := orbitalPolar_row i' f
  have j0 : sLocalOrbitalFourierJet i ((Kₛ(ω)).mkQ f) =
      iteratedDeriv 0 (fourierZeta(i.val.1) f) 0 := by
    have h := sLocalOrbitalFourierJet_mk i f
    rw [hi] at h
    exact h
  have j1 : sLocalOrbitalFourierJet i' ((Kₛ(ω)).mkQ f) =
      iteratedDeriv 1 (fourierZeta(i.val.1) f) 0 := by
    have h := sLocalOrbitalFourierJet_mk i' f
    rw [hi', hc] at h
    exact h
  rw [h0, hi] at r0
  rw [h1, hi', hc] at r1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.sub_zero, Nat.sub_self,
    Nat.factorial, Nat.cast_one, div_one, mul_one] at r0 r1
  rw [j0, j1]
  have ha := eq_inv_of_mul_eq_one_right r0.symm
  refine ⟨ha, ?_⟩
  rw [ha] at r1
  apply mul_left_cancel₀ hne
  field_simp
  field_simp at r1
  linear_combination -r1

/-- In a polar-biorthogonal system the term of an expansion at the leading coordinate of
a double pole has next Fourier jet minus the Laurent ratio times the leading Fourier jet
of the expanded class. -/
theorem sLocalPolarTerm_fourierJet_term {T : Finset V} {ω : PontryaginDual J₁}
    (i i' : I(T, ω)) (hi : i.val.2 = 0) (hc : i'.val.1 = i.val.1) (hi' : i'.val.2 = 1)
    (e x : Θₛ(ω)) (h0 : sLocalOrbitalPrincipalPart i e = 1)
    (h1 : sLocalOrbitalPrincipalPart i' e = 0) :
    sLocalOrbitalFourierJet i' (sLocalOrbitalPrincipalPart i x • e) =
      -(rhoCoeff(i.val.1, 1) / rhoCoeff(i.val.1, 0)) * sLocalOrbitalFourierJet i x := by
  obtain ⟨_, hj⟩ := sLocalPolarTerm_fourierJet i i' hi hc hi' e h0 h1
  obtain ⟨g, rfl⟩ := (Kₛ(ω)).mkQ_surjective x
  have hne := (orbitalPolar_leading i g).1
  have r0 := orbitalPolar_row i g
  have j0 : sLocalOrbitalFourierJet i ((Kₛ(ω)).mkQ g) =
      iteratedDeriv 0 (fourierZeta(i.val.1) g) 0 := by
    have h := sLocalOrbitalFourierJet_mk i g
    rw [hi] at h
    exact h
  rw [hi] at r0
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.sub_zero,
    Nat.factorial, Nat.cast_one, div_one] at r0
  rw [map_smul, hj, r0, j0, smul_eq_mul]
  field_simp

/-- In a Fréchet space the terms of a Schauder expansion tend to zero uniformly over a
pointwise bounded family of continuous functionals, by the uniform boundedness principle. -/
private theorem sLocalPolarTerm_terms_equicontinuous {Q ι : Type*} [AddCommGroup Q] [Module ℂ Q]
    [TopologicalSpace Q] [IsTopologicalAddGroup Q] [ContinuousSMul ℂ Q] (hQ : IsFrechetTVS Q)
    (e : ℕ → Q) (d : ℕ → StrongDual ℂ Q) (hb : IsSchauderBasis e d)
    (A : ι → StrongDual ℂ Q) (hbdd : ∀ y, ∃ C : ℝ, ∀ i, ‖A i y‖ ≤ C)
    (y : Q) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ i, ‖A i (d n y • e n)‖ ≤ ε := by
  let : BarrelledSpace ℂ Q := isFrechetTVS_barrelled hQ
  let : UniformSpace Q := IsTopologicalAddGroup.rightUniformSpace Q
  have : IsUniformAddGroup Q := isUniformAddGroup_of_addCommGroup
  have hequi : UniformEquicontinuous ((↑) ∘ A : ι → Q → ℂ) :=
    (norm_withSeminorms ℂ ℂ).banach_steinhaus (fun _ y ↦ by
      obtain ⟨C, hC⟩ := hbdd y
      exact ⟨C, by rintro _ ⟨i, rfl⟩; exact hC i⟩)
  have h0 := Metric.equicontinuousAt_iff_right.mp (hequi.equicontinuous 0) ε hε
  have hterms : Tendsto (fun n ↦ d n y • e n) atTop (𝓝 0) := by
    have h : HasSum (fun j ↦ d j y • e j) y (SummationFilter.conditional ℕ) := hb.2 y
    rw [HasSum, SummationFilter.conditional_filter_eq_map_range, tendsto_map'_iff] at h
    have h1 := (h.comp (tendsto_add_atTop_nat 1)).sub h
    rw [sub_self] at h1
    refine h1.congr fun n ↦ ?_
    simp [Finset.sum_range_succ]
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hterms.eventually h0)
  refine ⟨N, fun n hn i ↦ ?_⟩
  have h := hN n hn i
  simp only [Function.comp_apply, map_zero, dist_zero_left] at h
  exact h.le

open Classical in
/-- Paper: Theorem 7.3.1.6(2)–(3), pp. 345, 349.
If one enumeration of the polar coefficients has a biorthogonal Schauder basis of the
primary quotient, then along every pole lattice the ratio of the second to the leading
Laurent coefficient of the correcting factor, times the leading Fourier jet of any fixed
theta class, tends to zero over the centers of multiplicity at least two.
The Fréchet property of the primary quotient is a hypothesis here, so that the statement
does not depend on the closed-embedding theorem of §5.3. -/
theorem sLocalPolarOrbital_basis_ratio_tendsto_of_frechet
    (p : Vℚ) (ω : PontryaginDual J₁) (_hS : IsSaturatedPlaceSet S) (_hp : (Sₚ(p)).Nonempty)
    (_hPic : PicTrivial) (hQ : IsFrechetTVS (Q(p, ω)))
    (σ : ℕ ≃ Idx(p, ω)) (d : ℕ → StrongDual ℂ (Q(p, ω))) (e : ℕ → Q(p, ω))
    (hd : ∀ n x, d n (π(p, ω) x) =
      sLocalOrbitalPrincipalPart (F := F) (S := S) (T := Sₚ(p)) (ω := ω) (σ n) x)
    (hb : IsSchauderBasis e d)
    (χ : PontryaginDual Jₛ) (v : S) (u : (v.val.adicCompletion F)ˣ) (t : ℝ)
    (_hv : v.val ∈ Sₚ(p)) (_hu : uniformizerNorm(v, u)) (_ht : phase(χ, v, u, t))
    (x : Θₛ(ω)) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ (m : ℤ) (i' : Idx(p, ω)),
      (σ n).val = (lattice(χ, v, t, m), 0) → i'.val = (lattice(χ, v, t, m), 1) →
      v ∈ sLocalFinitePolePlaces (F := F) (S := S) (lattice(χ, v, t, m)) →
      ‖rhoCoeff((σ n).val.1, 1) / rhoCoeff((σ n).val.1, 0) *
        sLocalOrbitalFourierJet (F := F) (S := S) (T := Sₚ(p)) (ω := ω) (σ n) x‖ ≤ ε := by
  classical
  let ι := {i : Idx(p, ω) // ∃ m : ℤ, i.val = (lattice(χ, v, t, m), 1) ∧
    v ∈ sLocalFinitePolePlaces (F := F) (S := S) (lattice(χ, v, t, m))}
  let A (i : ι) : StrongDual ℂ (Q(p, ω)) :=
    (Rₚ(p, ω)).liftQL (sLocalOrbitalFourierJet (F := F) (S := S) (T := Sₚ(p)) (ω := ω) i.val)
      (sLocalOrbitalFourierJet_range_le_ker p ω i.val)
  have hA (i : ι) (z : Θₛ(ω)) : A i (π(p, ω) z) = sLocalOrbitalFourierJet i.val z := rfl
  have hbdd : ∀ y : Q(p, ω), ∃ C : ℝ, ∀ i : ι, ‖A i y‖ ≤ C := by
    intro y
    obtain ⟨z, rfl⟩ := (Rₚ(p, ω)).mkQ_surjective y
    obtain ⟨f, rfl⟩ := (Kₛ(ω)).mkQ_surjective z
    obtain ⟨C, -, hC⟩ := sLocalOrbitalFourierJet_lattice_schwartz_valueDecay
      (F := F) (S := S) p χ v u t _hS _hp _hPic _hv _hu _ht f 1 0
    refine ⟨C, ?_⟩
    rintro ⟨i, m, him, hpole⟩
    have hmult : 1 < sLocalPrimaryPoleMultiplicity (F := F) (S := S) p (lattice(χ, v, t, m)) := by
      have h := i.property.2
      rw [him] at h
      exact h
    have h := hC m
    rw [ite_eq_left_of_eq_true _ _ (eq_true (And.intro hpole hmult))] at h
    rw [hA]
    have hj := sLocalOrbitalFourierJet_mk i f
    rw [him] at hj
    change ‖sLocalOrbitalFourierJet i ((Kₛ(ω)).mkQL f)‖ ≤ C
    rw [hj]
    simpa using h
  obtain ⟨N, hN⟩ := sLocalPolarTerm_terms_equicontinuous hQ e d hb A hbdd (π(p, ω) x) ε hε
  refine ⟨N, fun n hn m i' h0' h1' hpole ↦ ?_⟩
  have hi : (σ n).val.2 = 0 := congrArg Prod.snd h0'
  have hc : i'.val.1 = (σ n).val.1 := (congrArg Prod.fst h1').trans (congrArg Prod.fst h0').symm
  have hi' : i'.val.2 = 1 := congrArg Prod.snd h1'
  obtain ⟨w, hw⟩ := (Rₚ(p, ω)).mkQ_surjective (e n)
  have hbi (k l : ℕ) : d k (e l) = if k = l then 1 else 0 := hb.1 k l
  have h0 : sLocalOrbitalPrincipalPart (σ n) w = 1 := by
    rw [← hd n w, hw, hbi]
    simp
  have h1 : sLocalOrbitalPrincipalPart i' w = 0 := by
    have hne : σ.symm i' ≠ n := by
      intro h
      have h2 : i' = σ n := by rw [← h, σ.apply_symm_apply]
      rw [h2, hi] at hi'
      exact zero_ne_one hi'
    have h := hd (σ.symm i') w
    rw [σ.apply_symm_apply, hw, hbi] at h
    rw [← h]
    simp [hne]
  have key := sLocalPolarTerm_fourierJet_term (σ n) i' hi hc hi' w x h0 h1
  have h := hN n hn ⟨i', m, h1', hpole⟩
  have hterm : d n (π(p, ω) x) • e n =
      π(p, ω) (sLocalOrbitalPrincipalPart (F := F) (S := S) (T := Sₚ(p)) (ω := ω) (σ n) x • w) := by
    rw [hd, ← hw]
    exact (map_smul (Rₚ(p, ω)).mkQ _ w).symm
  rw [hterm, hA, key, norm_mul, norm_neg] at h
  rw [norm_mul]
  exact h

open Classical in
/-- Paper: Theorem 7.3.1.6(2)–(3), pp. 345, 349.
The same statement with the Fréchet property taken from the library. -/
theorem sLocalPolarOrbital_basis_ratio_tendsto
    (p : Vℚ) (ω : PontryaginDual J₁) (_hS : IsSaturatedPlaceSet S) (_hp : (Sₚ(p)).Nonempty)
    (_hPic : PicTrivial)
    (σ : ℕ ≃ Idx(p, ω)) (d : ℕ → StrongDual ℂ (Q(p, ω))) (e : ℕ → Q(p, ω))
    (hd : ∀ n x, d n (π(p, ω) x) =
      sLocalOrbitalPrincipalPart (F := F) (S := S) (T := Sₚ(p)) (ω := ω) (σ n) x)
    (hb : IsSchauderBasis e d)
    (χ : PontryaginDual Jₛ) (v : S) (u : (v.val.adicCompletion F)ˣ) (t : ℝ)
    (_hv : v.val ∈ Sₚ(p)) (_hu : uniformizerNorm(v, u)) (_ht : phase(χ, v, u, t))
    (x : Θₛ(ω)) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ (m : ℤ) (i' : Idx(p, ω)),
      (σ n).val = (lattice(χ, v, t, m), 0) → i'.val = (lattice(χ, v, t, m), 1) →
      v ∈ sLocalFinitePolePlaces (F := F) (S := S) (lattice(χ, v, t, m)) →
      ‖rhoCoeff((σ n).val.1, 1) / rhoCoeff((σ n).val.1, 0) *
        sLocalOrbitalFourierJet (F := F) (S := S) (T := Sₚ(p)) (ω := ω) (σ n) x‖ ≤ ε :=
  sLocalPolarOrbital_basis_ratio_tendsto_of_frechet p ω _hS _hp _hPic
    (sLocalOrbitalSystem_quotient_nuclearFrechet (F := F) (S := S) p ω).1
    σ d e hd hb χ v u t _hv _hu _ht x ε hε

end LaurentNecessity

end RiemannMasullo

#print axioms RiemannMasullo.sLocalPolarTerm_fourierJet
#print axioms RiemannMasullo.sLocalPolarTerm_fourierJet_term
#print axioms RiemannMasullo.sLocalPolarOrbital_basis_ratio_tendsto_of_frechet
#print axioms RiemannMasullo.sLocalPolarOrbital_basis_ratio_tendsto
