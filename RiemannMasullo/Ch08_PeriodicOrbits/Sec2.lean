module

public import RiemannMasullo.AppA_AlgebraicNT.Sec2
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.Topology.Compactness.Paracompact
public import Mathlib.Topology.Separation.GDelta
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace

/-! # §8.2. Stack-theoretic periodic orbits and fixed points

The parameter `S` records the finite part of the paper's set of places. Every
infinite place is already included in `SAdeleRing`.
-/

@[expose] public noncomputable section

namespace RiemannMasullo

open Function IsDedekindDomain NumberField TopologicalSpace Topology
open scoped NNReal NumberField.AdeleRing

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

local notation "Aₛ" => SAdeleRing F S
local notation "𝕀ₛ" => (SAdeleRing F S)ˣ
local notation "Nₛ" => MonoidHom.ker (sIdeleNorm F S)
local notation "N₁" => MonoidHom.ker (ideleNorm F)

/-- Paper: Definition 8.2.0.1(1), p. 384. The base point $e_v$ has zero at $v$
and one elsewhere. The index `none` denotes the ordinary base point 1. -/
def adeleOrbitBasepoint : Option (InfinitePlace F ⊕ HeightOneSpectrum (𝓞 F)) → 𝔸[F]
  | none => 1
  | some (.inl v) => AdeleRing.ofCompletion (𝓞 F) F v 0
  | some (.inr v) => AdeleRing.ofAdicCompletion (𝓞 F) F v 0

/-- Paper: Definition 8.2.0.1(1), p. 384. Coordinate formulas for the global base points. -/
theorem adeleOrbitBasepoint_coordinates :
    adeleOrbitBasepoint F none = 1 ∧
      (∀ v : InfinitePlace F,
        (adeleOrbitBasepoint F (some (.inl v))).1 v = 0 ∧
        (∀ w : InfinitePlace F, w ≠ v → (adeleOrbitBasepoint F (some (.inl v))).1 w = 1) ∧
        (adeleOrbitBasepoint F (some (.inl v))).2 = 1) ∧
      (∀ v : HeightOneSpectrum (𝓞 F),
        (adeleOrbitBasepoint F (some (.inr v))).1 = 1 ∧
        (adeleOrbitBasepoint F (some (.inr v))).2 v = 0 ∧
        ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v →
          (adeleOrbitBasepoint F (some (.inr v))).2 w = 1) := by
  sorry

/-- Paper: Definition 8.2.0.1(1), p. 384. The S-local base points keep all infinite
places and the finite places in S. -/
def sAdeleOrbitBasepoint (i : Option (InfinitePlace F ⊕ S)) : Aₛ :=
  adeleProjection F S (adeleOrbitBasepoint F (i.map (Sum.map id Subtype.val)))

/-- Paper: Definition 8.2.0.1(1), p. 384. The base point at a selected finite place
has zero at that place, including after projection to the S-adeles. -/
theorem sAdeleOrbitBasepoint_finite (v : S) :
    (sAdeleOrbitBasepoint F S (some (.inr v))).2 v = 0 := by
  sorry

/-- Paper: Definition 8.2.0.1(1), p. 384. The set $Z_{F,S}$ in (8.2.0.1)
consists of 1 and the single-zero base points, with the adelic subspace topology. -/
def sAdeleOrbitBasepoints : Set Aₛ :=
  Set.range (sAdeleOrbitBasepoint F S)

/-- The index `none` gives the ordinary base point, since the projection is a ring hom. -/
private theorem sAdeleOrbitBasepoint_none : sAdeleOrbitBasepoint F S none = 1 := by
  simp [sAdeleOrbitBasepoint, adeleOrbitBasepoint]

/-- Paper: Definition 8.2.0.1(1), p. 384. The ordinary base point lies in $Z_{F,S}$. -/
theorem one_mem_sAdeleOrbitBasepoints : 1 ∈ sAdeleOrbitBasepoints F S :=
  ⟨none, sAdeleOrbitBasepoint_none F S⟩

/-- Paper: Definition 8.2.0.1(1), p. 384. The set $Z_F$ in (8.2.0.2)
consists of 1 and the single-zero base points, with the adelic subspace topology. -/
def adeleOrbitBasepoints : Set 𝔸[F] :=
  Set.range (adeleOrbitBasepoint F)

/-- Paper: Definition 8.2.0.1(1), p. 384. The ordinary base point lies in $Z_F$. -/
theorem one_mem_adeleOrbitBasepoints : 1 ∈ adeleOrbitBasepoints F := by
  sorry

/-- Paper: Definition 8.2.0.1(2), p. 384. The family in (8.2.0.3) consists of the
S-local full-idele orbits with their adelic subspace topologies. -/
def sAdeleFullOrbit (i : Option (InfinitePlace F ⊕ S)) : Set Aₛ :=
  MulAction.orbit 𝕀ₛ (sAdeleOrbitBasepoint F S i)

/-- Paper: Definition 8.2.0.1(2), p. 384. The ordinary S-local orbit consists of
the $S$-adeles that are units. -/
theorem mem_sAdeleFullOrbit_none_iff (x : Aₛ) :
    x ∈ sAdeleFullOrbit F S none ↔ IsUnit x := by
  rw [sAdeleFullOrbit, sAdeleOrbitBasepoint_none F S, MulAction.mem_orbit_iff]
  simp only [Units.smul_def, smul_eq_mul, mul_one]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u, hu⟩
  · rintro ⟨u, hu⟩
    exact ⟨u, hu⟩

/-- Paper: Definition 8.2.0.1(2), p. 384. The family in (8.2.0.4) consists of the
global full-idele orbits with their adelic subspace topologies. -/
def adeleFullOrbit (i : Option (InfinitePlace F ⊕ HeightOneSpectrum (𝓞 F))) : Set 𝔸[F] :=
  MulAction.orbit 𝔸[F]ˣ (adeleOrbitBasepoint F i)

/-- Paper: Definition 8.2.0.1(2), p. 384. The ordinary global orbit consists of
the adeles that are units. -/
theorem mem_adeleFullOrbit_none_iff (x : 𝔸[F]) :
    x ∈ adeleFullOrbit F none ↔ IsUnit x := by
  have h1 : adeleOrbitBasepoint F none = 1 := rfl
  rw [adeleFullOrbit, h1, MulAction.mem_orbit_iff]
  simp only [Units.smul_def, smul_eq_mul, mul_one]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u, hu⟩
  · rintro ⟨u, hu⟩
    exact ⟨u, hu⟩

/-- Paper: Definition 8.2.0.1(3), p. 385. The S-local set $D_{F,S}$ in (8.2.0.5)
is the union of the full-idele orbits with the adelic subspace topology. -/
def sAdeleFullOrbitUnion : Set Aₛ :=
  ⋃ i, sAdeleFullOrbit F S i

/-- Paper: Definition 8.2.0.1(3), p. 385. The S-local full-orbit union is the
set of translates of the special S-adeles by full ideles. -/
theorem mem_sAdeleFullOrbitUnion_iff (x : Aₛ) :
    x ∈ sAdeleFullOrbitUnion F S ↔
      ∃ (g : 𝕀ₛ) (z : sAdeleOrbitBasepoints F S), g • z.val = x := by
  simp only [sAdeleFullOrbitUnion, Set.mem_iUnion, sAdeleFullOrbit, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨i, g, hg⟩
    exact ⟨g, ⟨_, i, rfl⟩, hg⟩
  · rintro ⟨g, ⟨_, i, rfl⟩, hg⟩
    exact ⟨i, g, hg⟩

/-- Paper: Definition 8.2.0.1(3), p. 385. The global set $D_F$ in (8.2.0.5)
is the union of the full-idele orbits with the adelic subspace topology. -/
def adeleFullOrbitUnion : Set 𝔸[F] :=
  ⋃ i, adeleFullOrbit F i

/-- Paper: Definition 8.2.0.1(3), p. 385. The global full-orbit union is the
set of translates of the special adeles by full ideles. -/
theorem mem_adeleFullOrbitUnion_iff (x : 𝔸[F]) :
    x ∈ adeleFullOrbitUnion F ↔
      ∃ (g : 𝔸[F]ˣ) (z : adeleOrbitBasepoints F), g • z.val = x := by
  simp only [adeleFullOrbitUnion, Set.mem_iUnion, adeleFullOrbit, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨i, g, hg⟩
    exact ⟨g, ⟨_, i, rfl⟩, hg⟩
  · rintro ⟨g, ⟨_, i, rfl⟩, hg⟩
    exact ⟨i, g, hg⟩

-- Read the full-group stability sentence on p. 385 with (8.2.0.3)–(8.2.0.5).
-- The norm-one orbits in (8.2.0.6)–(8.2.0.8) are stable under the norm kernel.

/-- Paper: Definition 8.2.0.2(1), p. 385. The family in (8.2.0.6) consists of the
S-local norm-one orbits with their adelic subspace topologies. -/
def sAdeleNormOneOrbit (i : Option (InfinitePlace F ⊕ S)) : Set Aₛ :=
  MulAction.orbit Nₛ (sAdeleOrbitBasepoint F S i)

/-- Paper: Definition 8.2.0.2(1), p. 385. The ordinary S-local norm-one orbit
is the image of the norm kernel in the S-adeles. -/
theorem mem_sAdeleNormOneOrbit_none_iff (x : Aₛ) :
    x ∈ sAdeleNormOneOrbit F S none ↔
      ∃ g : 𝕀ₛ, sIdeleNorm F S g = 1 ∧ g.val = x := by
  rw [sAdeleNormOneOrbit, sAdeleOrbitBasepoint_none F S, MulAction.mem_orbit_iff]
  simp only [MulAction.subgroup_smul_def, Units.smul_def, smul_eq_mul, mul_one]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, MonoidHom.mem_ker.mp g.property, hg⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, MonoidHom.mem_ker.mpr hg⟩, rfl⟩

/-- Paper: Definition 8.2.0.2(1), p. 385. The family in (8.2.0.7) consists of the
global norm-one orbits with their adelic subspace topologies. -/
def adeleNormOneOrbit (i : Option (InfinitePlace F ⊕ HeightOneSpectrum (𝓞 F))) :
    Set 𝔸[F] :=
  MulAction.orbit N₁ (adeleOrbitBasepoint F i)

/-- Paper: Definition 8.2.0.2(1), p. 385. The ordinary global norm-one orbit is the
image of the norm kernel in the adeles. -/
theorem mem_adeleNormOneOrbit_none_iff (x : 𝔸[F]) :
    x ∈ adeleNormOneOrbit F none ↔ ∃ g : 𝔸[F]ˣ, ideleNorm F g = 1 ∧ g.val = x := by
  have h1 : adeleOrbitBasepoint F none = 1 := rfl
  rw [adeleNormOneOrbit, h1, MulAction.mem_orbit_iff]
  simp only [MulAction.subgroup_smul_def, Units.smul_def, smul_eq_mul, mul_one]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, MonoidHom.mem_ker.mp g.property, hg⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, MonoidHom.mem_ker.mpr hg⟩, rfl⟩

/-- Paper: Definition 8.2.0.2(2), p. 385. The S-local set $D^1_{F,S}$ in (8.2.0.8)
is the union of the norm-one orbits with the adelic subspace topology. -/
def sAdeleNormOneOrbitUnion : Set Aₛ :=
  ⋃ i, sAdeleNormOneOrbit F S i

/-- Paper: Definition 8.2.0.2(2), p. 385. An S-adele lies in the union exactly when
it is a norm-one translate of a special S-adele. -/
theorem mem_sAdeleNormOneOrbitUnion_iff (x : Aₛ) :
    x ∈ sAdeleNormOneOrbitUnion F S ↔
      ∃ (g : Nₛ) (z : sAdeleOrbitBasepoints F S), g • z.val = x := by
  simp only [sAdeleNormOneOrbitUnion, Set.mem_iUnion, sAdeleNormOneOrbit, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨i, g, hg⟩
    exact ⟨g, ⟨_, i, rfl⟩, hg⟩
  · rintro ⟨g, ⟨_, i, rfl⟩, hg⟩
    exact ⟨i, g, hg⟩

/-- Paper: Definition 8.2.0.2(2), p. 385. The global set $D^1_F$ in (8.2.0.8)
is the union of the norm-one orbits with the adelic subspace topology. -/
def adeleNormOneOrbitUnion : Set 𝔸[F] :=
  ⋃ i, adeleNormOneOrbit F i

/-- Paper: Definition 8.2.0.2(2), p. 385. An adele lies in the union exactly when
it is a norm-one translate of a special adele. -/
theorem mem_adeleNormOneOrbitUnion_iff (x : 𝔸[F]) :
    x ∈ adeleNormOneOrbitUnion F ↔
      ∃ (g : N₁) (z : adeleOrbitBasepoints F), g • z.val = x := by
  simp only [adeleNormOneOrbitUnion, Set.mem_iUnion, adeleNormOneOrbit, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨i, g, hg⟩
    exact ⟨g, ⟨_, i, rfl⟩, hg⟩
  · rintro ⟨g, ⟨_, i, rfl⟩, hg⟩
    exact ⟨i, g, hg⟩

/-- Paper: Lemma 8.2.0.3(1), p. 385. The S-local orbit map applies the norm-one
idele to the given special S-adele. -/
def sAdeleNormOneOrbitMap (gz : Nₛ × sAdeleOrbitBasepoints F S) :
    sAdeleNormOneOrbitUnion F S :=
  ⟨gz.1 • gz.2.val, (mem_sAdeleNormOneOrbitUnion_iff F S _).mpr ⟨gz.1, gz.2, rfl⟩⟩

/-- Paper: Lemma 8.2.0.3(1), p. 385. The underlying S-adele of the orbit map
is given by the norm-one action. -/
theorem sAdeleNormOneOrbitMap_val (g : Nₛ) (z : sAdeleOrbitBasepoints F S) :
    (sAdeleNormOneOrbitMap F S (g, z)).val = g • z.val := by
  rfl

/-- Paper: Lemma 8.2.0.3(2), p. 385. The global orbit map applies the norm-one
idele to the given special adele. -/
def adeleNormOneOrbitMap (gz : N₁ × adeleOrbitBasepoints F) : adeleNormOneOrbitUnion F :=
  ⟨gz.1 • gz.2.val, (mem_adeleNormOneOrbitUnion_iff F _).mpr ⟨gz.1, gz.2, rfl⟩⟩

/-- Paper: Lemma 8.2.0.3(2), p. 385. The underlying adele of the orbit map is
given by the norm-one action. -/
theorem adeleNormOneOrbitMap_val (g : N₁) (z : adeleOrbitBasepoints F) :
    (adeleNormOneOrbitMap F (g, z)).val = g • z.val := by
  rfl

/-- Convergence along an ultrafilter in a topological ring with a continuous multiplicative
gauge: elements of gauge one whose product with an idempotent converges to that idempotent
converge, once a compact set catches the complementary parts of bounded gauge. -/
private theorem sAdeleNormOneOrbitMap_isQuotientMap_core
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
    (ν : A → ℝ≥0) (hν : Continuous ν) (hνm : ∀ a b : A, ν (a * b) = ν a * ν b)
    (hν1 : ν 1 = 1) (e : A) (he : e * e = e) (K : Set A) (hK : IsCompact K)
    (hKe : ∀ t : A, t * e = 0 → ν (e + t) ≤ 2 → t ∈ K)
    {α : Type*} (𝒰 : Ultrafilter α) (q : α → A) (hq1 : ∀ p, ν (q p) = 1)
    (hqe : Filter.Tendsto (fun p ↦ q p * e) 𝒰 (𝓝 e)) :
    ∃ a : A, Filter.Tendsto q 𝒰 (𝓝 a) ∧ a * e = e ∧ ν a = 1 := by
  have hfac (x : A) : (x * e + (1 - e)) * (e + x * (1 - e)) = x := by
    linear_combination (2 * x - x * x - 1) * he
  have hlim : Filter.Tendsto (fun p ↦ ν (q p * e + (1 - e))) 𝒰 (𝓝 1) := by
    have h1 : Filter.Tendsto (fun p ↦ q p * e + (1 - e)) 𝒰 (𝓝 (e + (1 - e))) :=
      hqe.add_const (1 - e)
    rw [add_sub_cancel] at h1
    have h2 := (hν.tendsto 1).comp h1
    rw [hν1] at h2
    exact h2
  have hhalf : ∀ᶠ p in (𝒰 : Filter α), (1 / 2 : ℝ≥0) < ν (q p * e + (1 - e)) :=
    hlim.eventually (lt_mem_nhds (by norm_num))
  have hmemK : ∀ᶠ p in (𝒰 : Filter α), q p * (1 - e) ∈ K := by
    filter_upwards [hhalf] with p hp
    refine hKe _ (by linear_combination (-(q p)) * he) ?_
    by_contra hgt
    rw [not_le] at hgt
    have h3 : ν (q p * e + (1 - e)) * ν (e + q p * (1 - e)) = 1 := by
      rw [← hνm, hfac, hq1]
    have h4 : (1 / 2 : ℝ≥0) * 2 < ν (q p * e + (1 - e)) * ν (e + q p * (1 - e)) :=
      mul_lt_mul'' hp hgt zero_le zero_le
    rw [h3] at h4
    norm_num at h4
  have hle : ((𝒰.map fun p ↦ q p * (1 - e) : Ultrafilter A) : Filter A) ≤ Filter.principal K := by
    rw [Ultrafilter.coe_map, Filter.le_principal_iff]
    exact hmemK
  obtain ⟨b, -, hb⟩ := hK.ultrafilter_le_nhds _ hle
  rw [Ultrafilter.coe_map] at hb
  have hb' : Filter.Tendsto (fun p ↦ q p * (1 - e)) 𝒰 (𝓝 b) := hb
  have hbe : b * e = 0 := by
    refine tendsto_nhds_unique (hb'.mul_const e) ?_
    refine tendsto_const_nhds.congr fun p ↦ ?_
    linear_combination (q p) * he
  have hq : Filter.Tendsto q 𝒰 (𝓝 (e + b)) := (hqe.add hb').congr fun p ↦ by ring
  refine ⟨e + b, hq, ?_, ?_⟩
  · rw [add_mul, he, hbe, add_zero]
  · refine tendsto_nhds_unique ((hν.tendsto (e + b)).comp hq) ?_
    exact tendsto_const_nhds.congr fun p ↦ (hq1 p).symm

/-- Lifting of ultrafilter limits along the action of a gauge-one unit group on finitely
many idempotents: if the products converge to a point of the orbit union, the ultrafilter
converges to a preimage of that point. -/
private theorem sAdeleNormOneOrbitMap_isQuotientMap_lift
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
    (hind : IsInducing (Units.val : Aˣ → A))
    (ν : A → ℝ≥0) (hν : Continuous ν) (hνm : ∀ a b : A, ν (a * b) = ν a * ν b)
    (hν1 : ν 1 = 1) (hνu : ∀ a : A, ν a = 1 → IsUnit a)
    (N : Subgroup Aˣ) (hN : ∀ g : Aˣ, g ∈ N ↔ ν g.val = 1)
    (Z : Set A) (hZ : Z.Finite) (hidem : ∀ e ∈ Z, e * e = e)
    (hcomp : ∀ e ∈ Z, ∃ K : Set A, IsCompact K ∧
      ∀ t : A, t * e = 0 → ν (e + t) ≤ 2 → t ∈ K)
    (hsep : ∀ e ∈ Z, ∀ e' ∈ Z, e' * (1 - e) = 0 → ν e' = ν e → e' = e)
    (𝒰 : Ultrafilter (N × Z)) (h : N) (e' : Z)
    (hy : Filter.Tendsto (fun p : N × Z ↦ p.1.val.val * p.2.val) 𝒰
      (𝓝 (h.val.val * e'.val))) :
    ∃ x : N × Z, x.1.val.val * x.2.val = h.val.val * e'.val ∧
      (𝒰 : Filter (N × Z)) ≤ 𝓝 x := by
  have hfin : Finite Z := hZ.to_subtype
  obtain ⟨z₀, hz₀⟩ := (𝒰.map Prod.snd).eq_pure_of_finite
  have hev : ∀ᶠ p in (𝒰 : Filter (N × Z)), p.2 = z₀ := by
    have h1 : {z₀} ∈ ((𝒰.map Prod.snd : Ultrafilter Z) : Filter Z) := by
      rw [hz₀, Ultrafilter.coe_pure]
      exact Filter.mem_pure.2 (Set.mem_singleton z₀)
    rw [Ultrafilter.coe_map] at h1
    exact h1
  have he : z₀.val * z₀.val = z₀.val := hidem _ z₀.2
  have hy' : Filter.Tendsto (fun p : N × Z ↦ p.1.val.val * z₀.val) 𝒰
      (𝓝 (h.val.val * e'.val)) := by
    refine hy.congr' (hev.mono fun p hp ↦ ?_)
    show p.1.val.val * p.2.val = p.1.val.val * z₀.val
    rw [hp]
  have hq1 (p : N × Z) : ν (p.1.val.val * (h.val⁻¹ : Aˣ).val) = 1 :=
    (hN (p.1.val * h.val⁻¹)).mp (N.mul_mem p.1.2 (N.inv_mem h.2))
  have hqe' : Filter.Tendsto (fun p : N × Z ↦ p.1.val.val * (h.val⁻¹ : Aˣ).val * z₀.val) 𝒰
      (𝓝 e'.val) := by
    have h1 := hy'.mul_const ((h.val⁻¹ : Aˣ).val)
    have h2 : h.val.val * e'.val * (h.val⁻¹ : Aˣ).val = e'.val := by
      rw [mul_right_comm, Units.mul_inv, one_mul]
    rw [h2] at h1
    exact h1.congr fun p ↦ mul_right_comm _ _ _
  have hνe : ν e'.val = ν z₀.val := by
    refine tendsto_nhds_unique ((hν.tendsto _).comp hqe') ?_
    refine tendsto_const_nhds.congr fun p ↦ ?_
    show ν z₀.val = ν (p.1.val.val * (h.val⁻¹ : Aˣ).val * z₀.val)
    rw [hνm, hq1, one_mul]
  have hzero : e'.val * (1 - z₀.val) = 0 := by
    refine tendsto_nhds_unique (hqe'.mul_const (1 - z₀.val)) ?_
    refine tendsto_const_nhds.congr fun p ↦ ?_
    show (0 : A) = p.1.val.val * (h.val⁻¹ : Aˣ).val * z₀.val * (1 - z₀.val)
    linear_combination (p.1.val.val * (h.val⁻¹ : Aˣ).val) * he
  have heq : e'.val = z₀.val := hsep _ z₀.2 _ e'.2 hzero hνe
  rw [heq] at hqe'
  obtain ⟨K, hK, hKe⟩ := hcomp _ z₀.2
  obtain ⟨a, ha, hae, hνa⟩ := sAdeleNormOneOrbitMap_isQuotientMap_core ν hν hνm hν1 z₀.val he
    K hK hKe 𝒰 (fun p : N × Z ↦ p.1.val.val * (h.val⁻¹ : Aˣ).val) hq1 hqe'
  obtain ⟨u, hu⟩ := hνu a hνa
  have huN : u ∈ N := (hN u).mpr (by rw [hu]; exact hνa)
  have hNind : IsInducing (Units.val ∘ (Subtype.val : N → Aˣ)) :=
    hind.comp IsEmbedding.subtypeVal.toIsInducing
  refine ⟨(⟨u, huN⟩ * h, z₀), ?_, ?_⟩
  · show u.val * h.val.val * z₀.val = h.val.val * e'.val
    rw [hu, heq]
    linear_combination h.val.val * hae
  · rw [nhds_prod_eq, Filter.le_prod]
    constructor
    · refine hNind.tendsto_nhds_iff.2 ?_
      show Filter.Tendsto (fun p : N × Z ↦ p.1.val.val) 𝒰 (𝓝 (u.val * h.val.val))
      rw [hu]
      refine (ha.mul_const h.val.val).congr fun p ↦ ?_
      show p.1.val.val * (h.val⁻¹ : Aˣ).val * h.val.val = p.1.val.val
      rw [mul_assoc, Units.inv_mul, mul_one]
    · exact tendsto_const_nhds.congr' (hev.mono fun p hp ↦ hp.symm)

/-- The product of the normalized coordinate norms is continuous on the S-adele ring. -/
private theorem sAdeleNormOneOrbitMap_isQuotientMap_gauge_continuous
    (F : Type*) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) :
    Continuous (fun x : SAdeleRing F S ↦
      (∏ w : InfinitePlace F, ‖x.1 w‖₊ ^ w.mult) * ∏ v : S, ‖x.2 v‖₊) := by
  change Continuous (fun x : ((w : InfinitePlace F) → w.Completion) ×
    ((v : S) → (v.val.adicCompletion F)) ↦
    (∏ w : InfinitePlace F, ‖x.1 w‖₊ ^ w.mult) * ∏ v : S, ‖x.2 v‖₊)
  fun_prop

/-- The product of the normalized coordinate norms is multiplicative on the S-adele ring. -/
private theorem sAdeleNormOneOrbitMap_isQuotientMap_gauge_mul
    (F : Type*) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (a b : SAdeleRing F S) :
    (∏ w : InfinitePlace F, ‖(a * b).1 w‖₊ ^ w.mult) * ∏ v : S, ‖(a * b).2 v‖₊ =
      ((∏ w : InfinitePlace F, ‖a.1 w‖₊ ^ w.mult) * ∏ v : S, ‖a.2 v‖₊) *
        ((∏ w : InfinitePlace F, ‖b.1 w‖₊ ^ w.mult) * ∏ v : S, ‖b.2 v‖₊) := by
  have h1 (w : InfinitePlace F) : (a * b).1 w = a.1 w * b.1 w := rfl
  have h2 (v : S) : (a * b).2 v = a.2 v * b.2 v := rfl
  simp only [h1, h2, nnNorm_mul, mul_pow, Finset.prod_mul_distrib]
  ring

/-- The product of the normalized coordinate norms of the unit S-adele is one. -/
private theorem sAdeleNormOneOrbitMap_isQuotientMap_gauge_one
    (F : Type*) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) :
    (∏ w : InfinitePlace F, ‖(1 : SAdeleRing F S).1 w‖₊ ^ w.mult) *
      ∏ v : S, ‖(1 : SAdeleRing F S).2 v‖₊ = 1 := by
  have h1 (w : InfinitePlace F) : (1 : SAdeleRing F S).1 w = 1 := rfl
  have h2 (v : S) : (1 : SAdeleRing F S).2 v = 1 := rfl
  simp only [h1, h2, nnNorm_one, one_pow, Finset.prod_const_one, mul_one]

/-- An S-adele with nonzero product of coordinate norms has no zero coordinate. -/
private theorem sAdeleNormOneOrbitMap_isQuotientMap_gauge_ne_zero
    (F : Type*) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (a : SAdeleRing F S)
    (ha : (∏ w : InfinitePlace F, ‖a.1 w‖₊ ^ w.mult) * ∏ v : S, ‖a.2 v‖₊ ≠ 0) :
    (∀ w : InfinitePlace F, a.1 w ≠ 0) ∧ ∀ v : S, a.2 v ≠ 0 := by
  obtain ⟨hA, hB⟩ := mul_ne_zero_iff.mp ha
  refine ⟨fun w h0 ↦ ?_, fun v h0 ↦ ?_⟩
  · refine Finset.prod_ne_zero_iff.mp hA w (Finset.mem_univ w) ?_
    rw [h0, nnNorm_zero, zero_pow InfinitePlace.mult_pos.ne']
  · refine Finset.prod_ne_zero_iff.mp hB v (Finset.mem_univ v) ?_
    rw [h0, nnNorm_zero]

/-- An S-adele whose product of coordinate norms is one is a unit. -/
private theorem sAdeleNormOneOrbitMap_isQuotientMap_gauge_isUnit
    (F : Type*) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (a : SAdeleRing F S)
    (ha : (∏ w : InfinitePlace F, ‖a.1 w‖₊ ^ w.mult) * ∏ v : S, ‖a.2 v‖₊ = 1) :
    IsUnit a := by
  obtain ⟨h1, h2⟩ := sAdeleNormOneOrbitMap_isQuotientMap_gauge_ne_zero F S a
    (by rw [ha]; exact one_ne_zero)
  exact ⟨⟨a, (fun w ↦ (a.1 w)⁻¹, fun v ↦ (a.2 v)⁻¹),
    Prod.ext (funext fun w ↦ mul_inv_cancel₀ (h1 w)) (funext fun v ↦ mul_inv_cancel₀ (h2 v)),
    Prod.ext (funext fun w ↦ inv_mul_cancel₀ (h1 w)) (funext fun v ↦ inv_mul_cancel₀ (h2 v))⟩,
    rfl⟩

/-- An S-idele has norm one exactly when the product of its coordinate norms is one. -/
private theorem sAdeleNormOneOrbitMap_isQuotientMap_mem_ker
    (F : Type*) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (g : (SAdeleRing F S)ˣ) :
    g ∈ MonoidHom.ker (sIdeleNorm F S) ↔
      (∏ w : InfinitePlace F, ‖g.val.1 w‖₊ ^ w.mult) * ∏ v : S, ‖g.val.2 v‖₊ = 1 := by
  rw [MonoidHom.mem_ker, Units.ext_iff]
  simp only [sIdeleNorm, MonoidHom.mul_apply, MonoidHom.finsetProd_apply, MonoidHom.pow_apply,
    Units.val_mul, Units.coe_prod, Units.val_pow_eq_pow_val, Units.val_one]
  exact Iff.rfl

/-- Coordinates of the S-local base points: zero at the marked place, one elsewhere. -/
private theorem sAdeleNormOneOrbitMap_isQuotientMap_basepoint
    (F : Type*) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (i : Option (InfinitePlace F ⊕ S)) :
    (∀ w : InfinitePlace F,
      (i = some (.inl w) → (sAdeleOrbitBasepoint F S i).1 w = 0) ∧
      (i ≠ some (.inl w) → (sAdeleOrbitBasepoint F S i).1 w = 1)) ∧
    ∀ v : S,
      (i = some (.inr v) → (sAdeleOrbitBasepoint F S i).2 v = 0) ∧
      (i ≠ some (.inr v) → (sAdeleOrbitBasepoint F S i).2 v = 1) := by
  classical
  rcases i with _ | w' | v'
  · refine ⟨fun w ↦ ⟨fun h ↦ absurd h (by simp), fun _ ↦ ?_⟩,
      fun v ↦ ⟨fun h ↦ absurd h (by simp), fun _ ↦ ?_⟩⟩
    · rw [sAdeleOrbitBasepoint_none]
      rfl
    · rw [sAdeleOrbitBasepoint_none]
      rfl
  · refine ⟨fun w ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩, fun v ↦ ⟨fun h ↦ absurd h (by simp), fun _ ↦ rfl⟩⟩
    · obtain rfl : w' = w := Sum.inl.inj (Option.some.inj h)
      show Pi.mulSingle w' (0 : w'.Completion) w' = 0
      exact Pi.mulSingle_eq_same w' 0
    · show Pi.mulSingle w' (0 : w'.Completion) w = 1
      exact Pi.mulSingle_eq_of_ne (fun hw ↦ h (by rw [hw])) 0
  · refine ⟨fun w ↦ ⟨fun h ↦ absurd h (by simp), fun _ ↦ rfl⟩, fun v ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩⟩
    · obtain rfl : v' = v := Sum.inr.inj (Option.some.inj h)
      show Pi.mulSingle v'.val (0 : v'.val.adicCompletion F) v'.val = 0
      exact Pi.mulSingle_eq_same v'.val 0
    · show Pi.mulSingle v'.val (0 : v'.val.adicCompletion F) v.val = 1
      exact Pi.mulSingle_eq_of_ne (fun hv ↦ h (by rw [Subtype.ext hv])) 0

/-- Each S-local base point is idempotent. -/
private theorem sAdeleNormOneOrbitMap_isQuotientMap_idem
    (F : Type*) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (i : Option (InfinitePlace F ⊕ S)) :
    sAdeleOrbitBasepoint F S i * sAdeleOrbitBasepoint F S i = sAdeleOrbitBasepoint F S i := by
  classical
  obtain ⟨hb1, hb2⟩ := sAdeleNormOneOrbitMap_isQuotientMap_basepoint F S i
  refine Prod.ext (funext fun w ↦ ?_) (funext fun v ↦ ?_)
  · show (sAdeleOrbitBasepoint F S i).1 w * (sAdeleOrbitBasepoint F S i).1 w =
      (sAdeleOrbitBasepoint F S i).1 w
    by_cases h : i = some (.inl w)
    · rw [(hb1 w).1 h, mul_zero]
    · rw [(hb1 w).2 h, mul_one]
  · show (sAdeleOrbitBasepoint F S i).2 v * (sAdeleOrbitBasepoint F S i).2 v =
      (sAdeleOrbitBasepoint F S i).2 v
    by_cases h : i = some (.inr v)
    · rw [(hb2 v).1 h, mul_zero]
    · rw [(hb2 v).2 h, mul_one]

/-- Two S-local base points coincide once the first is supported on the second and their
products of coordinate norms agree. -/
private theorem sAdeleNormOneOrbitMap_isQuotientMap_sep
    (F : Type*) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (i j : Option (InfinitePlace F ⊕ S))
    (h0 : sAdeleOrbitBasepoint F S j * (1 - sAdeleOrbitBasepoint F S i) = 0)
    (hg : (∏ w : InfinitePlace F, ‖(sAdeleOrbitBasepoint F S j).1 w‖₊ ^ w.mult) *
        ∏ v : S, ‖(sAdeleOrbitBasepoint F S j).2 v‖₊ =
      (∏ w : InfinitePlace F, ‖(sAdeleOrbitBasepoint F S i).1 w‖₊ ^ w.mult) *
        ∏ v : S, ‖(sAdeleOrbitBasepoint F S i).2 v‖₊) :
    sAdeleOrbitBasepoint F S j = sAdeleOrbitBasepoint F S i := by
  classical
  obtain ⟨hi1, hi2⟩ := sAdeleNormOneOrbitMap_isQuotientMap_basepoint F S i
  obtain ⟨hj1, hj2⟩ := sAdeleNormOneOrbitMap_isQuotientMap_basepoint F S j
  rcases i with _ | w | v
  · rw [sAdeleOrbitBasepoint_none, sAdeleNormOneOrbitMap_isQuotientMap_gauge_one] at hg
    obtain ⟨hn1, hn2⟩ := sAdeleNormOneOrbitMap_isQuotientMap_gauge_ne_zero F S _
      (by rw [hg]; exact one_ne_zero)
    rcases j with _ | w | v
    · rfl
    · exact absurd ((hj1 w).1 rfl) (hn1 w)
    · exact absurd ((hj2 v).1 rfl) (hn2 v)
  · have h1 : (sAdeleOrbitBasepoint F S j).1 w *
        (1 - (sAdeleOrbitBasepoint F S (some (.inl w))).1 w) = 0 :=
      congrFun (congrArg Prod.fst h0) w
    rw [(hi1 w).1 rfl, sub_zero, mul_one] at h1
    have hj : j = some (.inl w) := by
      by_contra hne
      rw [(hj1 w).2 hne] at h1
      exact one_ne_zero h1
    rw [hj]
  · have h1 : (sAdeleOrbitBasepoint F S j).2 v *
        (1 - (sAdeleOrbitBasepoint F S (some (.inr v))).2 v) = 0 :=
      congrFun (congrArg Prod.snd h0) v
    rw [(hi2 v).1 rfl, sub_zero, mul_one] at h1
    have hj : j = some (.inr v) := by
      by_contra hne
      rw [(hj2 v).2 hne] at h1
      exact one_ne_zero h1
    rw [hj]

/-- Boxes in the S-adele ring are compact: closed balls of the archimedean completions are
compact through the isometric embedding into the complex numbers, those of the finite
completions because these are proper. -/
private theorem sAdeleNormOneOrbitMap_isQuotientMap_isCompact_box
    (F : Type*) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (R : ℝ) :
    IsCompact {t : SAdeleRing F S |
      (∀ w : InfinitePlace F, ‖t.1 w‖ ≤ R) ∧ ∀ v : S, ‖t.2 v‖ ≤ R} := by
  have h1 : IsCompact (Set.univ.pi fun w : InfinitePlace F ↦
      Metric.closedBall (0 : w.Completion) R) := by
    refine isCompact_univ_pi fun w ↦ ?_
    have hiso := InfinitePlace.Completion.isometry_extensionEmbedding w
    have h0 := hiso.preimage_closedBall (0 : w.Completion) R
    rw [map_zero] at h0
    rw [← h0]
    exact hiso.isClosedEmbedding.isCompact_preimage (isCompact_closedBall 0 R)
  have h2 : IsCompact (Set.univ.pi fun v : S ↦
      Metric.closedBall (0 : v.val.adicCompletion F) R) := by
    refine isCompact_univ_pi fun v ↦ ?_
    have := properSpace_adicCompletion (K := F) v.val
    exact isCompact_closedBall 0 R
  have hK : {t : ((w : InfinitePlace F) → w.Completion) × ((v : S) → (v.val.adicCompletion F)) |
      (∀ w : InfinitePlace F, ‖t.1 w‖ ≤ R) ∧ ∀ v : S, ‖t.2 v‖ ≤ R} =
      (Set.univ.pi fun w : InfinitePlace F ↦ Metric.closedBall (0 : w.Completion) R) ×ˢ
        (Set.univ.pi fun v : S ↦ Metric.closedBall (0 : v.val.adicCompletion F) R) := by
    ext t
    constructor
    · rintro ⟨ha, hb⟩
      exact ⟨fun w _ ↦ mem_closedBall_zero_iff.mpr (ha w),
        fun v _ ↦ mem_closedBall_zero_iff.mpr (hb v)⟩
    · rintro ⟨ha, hb⟩
      exact ⟨fun w ↦ mem_closedBall_zero_iff.mp (ha w (Set.mem_univ w)),
        fun v ↦ mem_closedBall_zero_iff.mp (hb v (Set.mem_univ v))⟩
  change IsCompact {t : ((w : InfinitePlace F) → w.Completion) ×
    ((v : S) → (v.val.adicCompletion F)) |
      (∀ w : InfinitePlace F, ‖t.1 w‖ ≤ R) ∧ ∀ v : S, ‖t.2 v‖ ≤ R}
  rw [hK]
  exact h1.prod h2

/-- An S-adele killed by a base point, whose sum with the base point has product of
coordinate norms at most two, lies in the box of radius two. -/
private theorem sAdeleNormOneOrbitMap_isQuotientMap_bound
    (F : Type*) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (i : Option (InfinitePlace F ⊕ S)) (t : SAdeleRing F S)
    (ht : t * sAdeleOrbitBasepoint F S i = 0)
    (hg : (∏ w : InfinitePlace F, ‖(sAdeleOrbitBasepoint F S i + t).1 w‖₊ ^ w.mult) *
      ∏ v : S, ‖(sAdeleOrbitBasepoint F S i + t).2 v‖₊ ≤ 2) :
    (∀ w : InfinitePlace F, ‖t.1 w‖ ≤ 2) ∧ ∀ v : S, ‖t.2 v‖ ≤ 2 := by
  classical
  obtain ⟨hb1, hb2⟩ := sAdeleNormOneOrbitMap_isQuotientMap_basepoint F S i
  have hz1 (w : InfinitePlace F) (h : i ≠ some (.inl w)) : t.1 w = 0 := by
    have h1 : t.1 w * (sAdeleOrbitBasepoint F S i).1 w = 0 :=
      congrFun (congrArg Prod.fst ht) w
    rwa [(hb1 w).2 h, mul_one] at h1
  have hz2 (v : S) (h : i ≠ some (.inr v)) : t.2 v = 0 := by
    have h1 : t.2 v * (sAdeleOrbitBasepoint F S i).2 v = 0 :=
      congrFun (congrArg Prod.snd ht) v
    rwa [(hb2 v).2 h, mul_one] at h1
  have hf1 (w : InfinitePlace F) (h : i ≠ some (.inl w)) :
      ‖(sAdeleOrbitBasepoint F S i + t).1 w‖₊ ^ w.mult = 1 := by
    have h1 : (sAdeleOrbitBasepoint F S i + t).1 w = 1 := by
      show (sAdeleOrbitBasepoint F S i).1 w + t.1 w = 1
      rw [(hb1 w).2 h, hz1 w h, add_zero]
    rw [h1, nnNorm_one, one_pow]
  have hf2 (v : S) (h : i ≠ some (.inr v)) :
      ‖(sAdeleOrbitBasepoint F S i + t).2 v‖₊ = 1 := by
    have h1 : (sAdeleOrbitBasepoint F S i + t).2 v = 1 := by
      show (sAdeleOrbitBasepoint F S i).2 v + t.2 v = 1
      rw [(hb2 v).2 h, hz2 v h, add_zero]
    rw [h1, nnNorm_one]
  refine ⟨fun w ↦ ?_, fun v ↦ ?_⟩
  · by_cases h : i = some (.inl w)
    · have hP1 : ∏ w' : InfinitePlace F, ‖(sAdeleOrbitBasepoint F S i + t).1 w'‖₊ ^ w'.mult =
          ‖(sAdeleOrbitBasepoint F S i + t).1 w‖₊ ^ w.mult :=
        Finset.prod_eq_single w
          (fun w' _ hw' ↦ hf1 w' fun h' ↦ hw' (Sum.inl.inj (Option.some.inj (h'.symm.trans h))))
          (fun hn ↦ absurd (Finset.mem_univ w) hn)
      have hP2 : ∏ v : S, ‖(sAdeleOrbitBasepoint F S i + t).2 v‖₊ = 1 :=
        Finset.prod_eq_one fun v _ ↦
          hf2 v fun h' ↦ Sum.inl_ne_inr (Option.some.inj (h.symm.trans h'))
      have h1 : (sAdeleOrbitBasepoint F S i + t).1 w = t.1 w := by
        show (sAdeleOrbitBasepoint F S i).1 w + t.1 w = t.1 w
        rw [(hb1 w).1 h, zero_add]
      rw [hP1, hP2, mul_one, h1] at hg
      by_contra hgt
      rw [not_le] at hgt
      have h3 : (2 : ℝ≥0) < ‖t.1 w‖₊ := by exact_mod_cast hgt
      have h4 : ‖t.1 w‖₊ ≤ ‖t.1 w‖₊ ^ w.mult :=
        le_self_pow₀ (le_trans (by norm_num) h3.le) InfinitePlace.mult_pos.ne'
      exact absurd (h4.trans hg) (not_le.mpr h3)
    · rw [hz1 w h, norm_zero]
      norm_num
  · by_cases h : i = some (.inr v)
    · have hP1 : ∏ w : InfinitePlace F, ‖(sAdeleOrbitBasepoint F S i + t).1 w‖₊ ^ w.mult = 1 :=
        Finset.prod_eq_one fun w _ ↦
          hf1 w fun h' ↦ Sum.inl_ne_inr (Option.some.inj (h'.symm.trans h))
      have hP2 : ∏ v' : S, ‖(sAdeleOrbitBasepoint F S i + t).2 v'‖₊ =
          ‖(sAdeleOrbitBasepoint F S i + t).2 v‖₊ :=
        Finset.prod_eq_single v
          (fun v' _ hv' ↦ hf2 v' fun h' ↦ hv' (Sum.inr.inj (Option.some.inj (h'.symm.trans h))))
          (fun hn ↦ absurd (Finset.mem_univ v) hn)
      have h1 : (sAdeleOrbitBasepoint F S i + t).2 v = t.2 v := by
        show (sAdeleOrbitBasepoint F S i).2 v + t.2 v = t.2 v
        rw [(hb2 v).1 h, zero_add]
      rw [hP1, hP2, one_mul, h1] at hg
      exact_mod_cast hg
    · rw [hz2 v h, norm_zero]
      norm_num

/-- The S-local orbit map is proper: an ultrafilter on the source whose image converges in
the orbit union converges to a preimage of the limit. -/
private theorem sAdeleNormOneOrbitMap_isQuotientMap_isProperMap
    (F : Type*) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) :
    IsProperMap (sAdeleNormOneOrbitMap F S) := by
  have hT2 : T2Space (SAdeleRing F S) := by
    change T2Space
      (((w : InfinitePlace F) → w.Completion) × ((v : S) → (v.val.adicCompletion F)))
    infer_instance
  have hc : Continuous (sAdeleNormOneOrbitMap F S) := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_subtype_val.comp continuous_fst).smul
      (continuous_subtype_val.comp continuous_snd)
  rw [isProperMap_iff_ultrafilter]
  refine ⟨hc, fun 𝒰 y hy ↦ ?_⟩
  obtain ⟨h, z, hhz⟩ := (mem_sAdeleNormOneOrbitUnion_iff F S y.val).mp y.2
  have hy' : Filter.Tendsto
      (fun p : MonoidHom.ker (sIdeleNorm F S) × sAdeleOrbitBasepoints F S ↦
        p.1.val.val * p.2.val) 𝒰 (𝓝 (h.val.val * z.val)) := by
    have h1 := (continuous_subtype_val.tendsto y).comp hy
    have h2 : y.val = h.val.val * z.val := hhz.symm
    rw [h2] at h1
    exact h1
  obtain ⟨x, hx, hxU⟩ := sAdeleNormOneOrbitMap_isQuotientMap_lift
    (sIdeleGroup_description F S).1
    (fun x : SAdeleRing F S ↦
      (∏ w : InfinitePlace F, ‖x.1 w‖₊ ^ w.mult) * ∏ v : S, ‖x.2 v‖₊)
    (sAdeleNormOneOrbitMap_isQuotientMap_gauge_continuous F S)
    (sAdeleNormOneOrbitMap_isQuotientMap_gauge_mul F S)
    (sAdeleNormOneOrbitMap_isQuotientMap_gauge_one F S)
    (sAdeleNormOneOrbitMap_isQuotientMap_gauge_isUnit F S)
    (MonoidHom.ker (sIdeleNorm F S))
    (sAdeleNormOneOrbitMap_isQuotientMap_mem_ker F S)
    (sAdeleOrbitBasepoints F S) (Set.finite_range _)
    (by
      rintro _ ⟨i, rfl⟩
      exact sAdeleNormOneOrbitMap_isQuotientMap_idem F S i)
    (by
      rintro _ ⟨i, rfl⟩
      exact ⟨_, sAdeleNormOneOrbitMap_isQuotientMap_isCompact_box F S 2,
        fun t ht hg ↦ sAdeleNormOneOrbitMap_isQuotientMap_bound F S i t ht hg⟩)
    (by
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ h0 hg
      exact sAdeleNormOneOrbitMap_isQuotientMap_sep F S i j h0 hg)
    𝒰 h z hy'
  exact ⟨x, Subtype.ext (hx.trans hhz), hxU⟩

/-- Paper: Lemma 8.2.0.3(1), p. 385. The adelic subspace topology on the S-local
norm-one orbit union is the quotient topology of the S-local orbit map. -/
theorem sAdeleNormOneOrbitMap_isQuotientMap : IsQuotientMap (sAdeleNormOneOrbitMap F S) := by
  have hp := sAdeleNormOneOrbitMap_isQuotientMap_isProperMap F S
  refine hp.isClosedMap.isQuotientMap hp.toContinuous ?_
  rintro ⟨x, hx⟩
  obtain ⟨g, z, hgz⟩ := (mem_sAdeleNormOneOrbitUnion_iff F S x).mp hx
  exact ⟨(g, z), Subtype.ext hgz⟩

/-- Paper: Lemma 8.2.0.3(2), p. 385. The global orbit map is continuous for the
adelic subspace topology on the target.
Deviation: The adelic subspace topology is coarser than the quotient topology.
The equality of topologies fails by ERRATA R12. -/
theorem adeleNormOneOrbitMap_continuous : Continuous (adeleNormOneOrbitMap F) := by
  refine Continuous.subtype_mk ?_ _
  exact (continuous_subtype_val.comp continuous_fst).smul
    (continuous_subtype_val.comp continuous_snd)

/-- Paper: Lemma 8.2.0.3(2), p. 385. Every point in the global norm-one orbit union
has a preimage under the orbit map. -/
theorem adeleNormOneOrbitMap_surjective : Surjective (adeleNormOneOrbitMap F) := by
  rintro ⟨x, hx⟩
  simp only [adeleNormOneOrbitUnion, Set.mem_iUnion] at hx
  obtain ⟨i, hi⟩ := hx
  simp only [adeleNormOneOrbit, MulAction.mem_orbit_iff] at hi
  obtain ⟨g, hg⟩ := hi
  exact ⟨(g, ⟨adeleOrbitBasepoint F i, Set.mem_range_self i⟩), Subtype.ext hg⟩

/-- Paper: Lemma 8.2.0.3(2), p. 385. The global orbit map is an open quotient map
for its coinduced topology.
Deviation: The target carries the quotient topology of the global orbit map.
ERRATA R12 distinguishes this topology from the adelic subspace topology. -/
theorem adeleNormOneOrbitMap_isOpenQuotientMap :
    @IsOpenQuotientMap _ _ inferInstance
      (TopologicalSpace.coinduced (adeleNormOneOrbitMap F) inferInstance)
      (adeleNormOneOrbitMap F) := by
  sorry

/-- The S-adele ring is Hausdorff: it is a product of Hausdorff completions of `F`.
The instance has to be routed through the definition, exactly as in
`AppA_AlgebraicNT/Sec1.lean` (`adeleHausdorff_ideleLocallyCompact`). -/
private theorem t2Space_sAdeleRing : T2Space (SAdeleRing F S) := by
  change T2Space (((w : InfinitePlace F) → w.Completion) × ((v : S) → (v.val.adicCompletion F)))
  infer_instance

/-- Paper: Lemma 8.2.0.3, p. 385. The S-local norm-one orbit union is Hausdorff. -/
theorem sAdeleNormOneOrbitUnion_t2Space : T2Space (sAdeleNormOneOrbitUnion F S) := by
  have := t2Space_sAdeleRing F S
  infer_instance

/-- The adele ring is Hausdorff: a product of the infinite part with the restricted
product of the finite part. The restricted product instance only fires after unfolding,
so it is written out (`Πʳ` is not in scope in this file). -/
private theorem t2Space_adeleRing : T2Space 𝔸[F] :=
  inferInstanceAs (T2Space (((w : InfinitePlace F) → w.Completion) ×
    RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletionIntegers F) Filter.cofinite))

/-- Paper: Lemma 8.2.0.3, p. 385. The global norm-one orbit union is Hausdorff. -/
theorem adeleNormOneOrbitUnion_t2Space : T2Space (adeleNormOneOrbitUnion F) := by
  have := t2Space_adeleRing F
  infer_instance

/-- Paper: Lemma 8.2.0.3, p. 385. The S-local norm-one orbit union is metrizable. -/
theorem sAdeleNormOneOrbitUnion_metrizableSpace :
    MetrizableSpace (sAdeleNormOneOrbitUnion F S) := by
  sorry

/-- Paper: Lemma 8.2.0.3, p. 385. The global norm-one orbit union is metrizable. -/
theorem adeleNormOneOrbitUnion_metrizableSpace : MetrizableSpace (adeleNormOneOrbitUnion F) := by
  sorry

/-- Paper: Lemma 8.2.0.3, p. 385. The S-local norm-one orbit union is second-countable. -/
theorem sAdeleNormOneOrbitUnion_secondCountable :
    SecondCountableTopology (sAdeleNormOneOrbitUnion F S) := by
  sorry

/-- Paper: Lemma 8.2.0.3, p. 385. The global norm-one orbit union is second-countable. -/
theorem adeleNormOneOrbitUnion_secondCountable :
    SecondCountableTopology (adeleNormOneOrbitUnion F) := by
  sorry

/-- Paper: Lemma 8.2.0.3, p. 385. The S-local norm-one orbit union is perfectly normal. -/
theorem sAdeleNormOneOrbitUnion_perfectlyNormal :
    PerfectlyNormalSpace (sAdeleNormOneOrbitUnion F S) := by
  have h : MetrizableSpace (SAdeleRing F S) := by
    change MetrizableSpace
      (((w : InfinitePlace F) → w.Completion) × ((v : S) → (v.val.adicCompletion F)))
    infer_instance
  infer_instance

/-- Paper: Lemma 8.2.0.3, p. 385. The global norm-one orbit union is perfectly normal. -/
theorem adeleNormOneOrbitUnion_perfectlyNormal :
    PerfectlyNormalSpace (adeleNormOneOrbitUnion F) := by
  sorry

/-- The S-adele ring is second countable: each infinite completion embeds isometrically
in the complex numbers, and each finite completion is a proper metric space. -/
private theorem sAdeleNormOneOrbitUnion_separableSpace_secondCountable
    (F : Type*) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) :
    SecondCountableTopology (SAdeleRing F S) := by
  have h1 (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  have h2 (v : S) : SecondCountableTopology (v.val.adicCompletion F) := by
    have := properSpace_adicCompletion (K := F) v.val
    infer_instance
  change SecondCountableTopology
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → (v.val.adicCompletion F)))
  infer_instance

/-- Paper: Lemma 8.2.0.3, p. 385. The S-local norm-one orbit union is separable. -/
theorem sAdeleNormOneOrbitUnion_separableSpace : SeparableSpace (sAdeleNormOneOrbitUnion F S) := by
  have := sAdeleNormOneOrbitUnion_separableSpace_secondCountable F S
  infer_instance

/-- Paper: Lemma 8.2.0.3, p. 385. The global norm-one orbit union is separable. -/
theorem adeleNormOneOrbitUnion_separableSpace : SeparableSpace (adeleNormOneOrbitUnion F) := by
  sorry

/-- A proper surjection from a weakly locally compact space has a weakly locally compact
target: the image of a compact neighbourhood of a fibre is a compact neighbourhood. -/
private theorem sAdeleNormOneOrbitUnion_locallyCompactSpace_of_isProperMap
    {X : Type*} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [WeaklyLocallyCompactSpace X] (f : X → Y) (hf : IsProperMap f)
    (hs : Function.Surjective f) : WeaklyLocallyCompactSpace Y := by
  refine ⟨fun y ↦ ?_⟩
  obtain ⟨K, hK, hKi⟩ :=
    exists_compact_superset (hf.isCompact_preimage (isCompact_singleton (x := y)))
  refine ⟨f '' K, hK.image hf.toContinuous, ?_⟩
  have hcl : IsClosed (f '' (interior K)ᶜ) :=
    hf.isClosedMap _ isOpen_interior.isClosed_compl
  have hy : y ∈ (f '' (interior K)ᶜ)ᶜ := by
    rintro ⟨x, hx, rfl⟩
    exact hx (hKi (Set.mem_singleton (f x)))
  refine Filter.mem_of_superset (hcl.isOpen_compl.mem_nhds hy) ?_
  intro y' hy'
  obtain ⟨x, rfl⟩ := hs y'
  refine ⟨x, ?_, rfl⟩
  by_contra hx
  exact hy' ⟨x, fun hxi ↦ hx (interior_subset hxi), rfl⟩

/-- Paper: Lemma 8.2.0.3, p. 385. The S-local norm-one orbit union is locally compact. -/
theorem sAdeleNormOneOrbitUnion_locallyCompactSpace :
    LocallyCompactSpace (sAdeleNormOneOrbitUnion F S) := by
  have hT2 := t2Space_sAdeleRing F S
  have hp := sAdeleNormOneOrbitMap_isQuotientMap_isProperMap F S
  have hs : Surjective (sAdeleNormOneOrbitMap F S) := by
    rintro ⟨x, hx⟩
    obtain ⟨g, z, hgz⟩ := (mem_sAdeleNormOneOrbitUnion_iff F S x).mp hx
    exact ⟨(g, z), Subtype.ext hgz⟩
  have h4 : LocallyCompactSpace (SAdeleRing F S)ˣ := (sIdeleGroup_description F S).2.2.1
  have hcl : IsClosed ((MonoidHom.ker (sIdeleNorm F S) : Subgroup (SAdeleRing F S)ˣ) :
      Set (SAdeleRing F S)ˣ) := by
    have h1 : ((MonoidHom.ker (sIdeleNorm F S) : Subgroup (SAdeleRing F S)ˣ) :
        Set (SAdeleRing F S)ˣ) = (fun g : (SAdeleRing F S)ˣ ↦
          (∏ w : InfinitePlace F, ‖g.val.1 w‖₊ ^ w.mult) * ∏ v : S, ‖g.val.2 v‖₊) ⁻¹' {1} := by
      ext g
      exact sAdeleNormOneOrbitMap_isQuotientMap_mem_ker F S g
    rw [h1]
    exact isClosed_singleton.preimage
      ((sAdeleNormOneOrbitMap_isQuotientMap_gauge_continuous F S).comp Units.continuous_val)
  have h5 : LocallyCompactSpace (MonoidHom.ker (sIdeleNorm F S)) := hcl.locallyCompactSpace
  have h6 : Finite (sAdeleOrbitBasepoints F S) :=
    (Set.finite_range (sAdeleOrbitBasepoint F S)).to_subtype
  have h7 : WeaklyLocallyCompactSpace (sAdeleNormOneOrbitUnion F S) :=
    sAdeleNormOneOrbitUnion_locallyCompactSpace_of_isProperMap _ hp hs
  infer_instance

/-- Paper: Lemma 8.2.0.3, p. 385. The global norm-one orbit union is locally compact
in the quotient topology of the orbit map.
Deviation: The adelic subspace topology fails to be locally compact by ERRATA R13. -/
theorem adeleNormOneOrbitUnion_locallyCompactSpace :
    @LocallyCompactSpace (adeleNormOneOrbitUnion F)
      (TopologicalSpace.coinduced (adeleNormOneOrbitMap F) inferInstance) := by
  sorry

/-- The S-idelic norm is continuous: it is a finite product of powers of coordinate norms. -/
private theorem sAdeleNormOneOrbitUnion_sigmaCompactSpace_continuous
    (F : Type*) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) :
    Continuous (sIdeleNorm F S) := by
  apply Units.isEmbedding_val₀.continuous_iff.mpr
  change Continuous (fun g : (SAdeleRing F S)ˣ ↦ ((sIdeleNorm F S g).val))
  simp only [sIdeleNorm, MonoidHom.mul_apply, MonoidHom.finsetProd_apply, MonoidHom.pow_apply,
    Units.val_mul, Units.coe_prod, Units.val_pow_eq_pow_val]
  change Continuous (fun g : (SAdeleRing F S)ˣ ↦
    (∏ w : InfinitePlace F, ‖g.val.1 w‖₊ ^ w.mult) * ∏ v : S, ‖g.val.2 v‖₊)
  fun_prop

/-- The norm-one subgroup of the S-ideles is σ-compact: it is closed in the S-idele group,
which is locally compact and second countable. -/
private theorem sAdeleNormOneOrbitUnion_sigmaCompactSpace_kernel
    (F : Type*) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) :
    SigmaCompactSpace (MonoidHom.ker (sIdeleNorm F S)) := by
  have h2 := sAdeleNormOneOrbitUnion_separableSpace_secondCountable F S
  have hd := sIdeleGroup_description F S
  have h3 : SecondCountableTopology (SAdeleRing F S)ˣ := hd.1.secondCountableTopology
  have h4 : LocallyCompactSpace (SAdeleRing F S)ˣ := hd.2.2.1
  have h5 : SigmaCompactSpace (SAdeleRing F S)ˣ := inferInstance
  have hcl : IsClosed ((MonoidHom.ker (sIdeleNorm F S) : Subgroup (SAdeleRing F S)ˣ) :
      Set (SAdeleRing F S)ˣ) := by
    rw [MonoidHom.coe_ker]
    exact isClosed_singleton.preimage
      (sAdeleNormOneOrbitUnion_sigmaCompactSpace_continuous F S)
  exact hcl.sigmaCompactSpace

/-- Paper: Lemma 8.2.0.3, p. 385. The S-local norm-one orbit union is σ-compact. -/
theorem sAdeleNormOneOrbitUnion_sigmaCompactSpace :
    SigmaCompactSpace (sAdeleNormOneOrbitUnion F S) := by
  have h1 := sAdeleNormOneOrbitUnion_sigmaCompactSpace_kernel F S
  have h2 : Finite (sAdeleOrbitBasepoints F S) :=
    (Set.finite_range (sAdeleOrbitBasepoint F S)).to_subtype
  have hc : Continuous (sAdeleNormOneOrbitMap F S) := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_subtype_val.comp continuous_fst).smul
      (continuous_subtype_val.comp continuous_snd)
  have hs : Surjective (sAdeleNormOneOrbitMap F S) := by
    rintro ⟨x, hx⟩
    obtain ⟨g, z, hgz⟩ := (mem_sAdeleNormOneOrbitUnion_iff F S x).mp hx
    exact ⟨(g, z), Subtype.ext hgz⟩
  have hr := isSigmaCompact_range hc
  rw [hs.range_eq] at hr
  exact isSigmaCompact_univ_iff.mp hr

/-- Paper: Lemma 8.2.0.3, p. 385. The global norm-one orbit union is σ-compact
in the adelic subspace topology. -/
theorem adeleNormOneOrbitUnion_sigmaCompactSpace :
    SigmaCompactSpace (adeleNormOneOrbitUnion F) := by
  sorry

/-- Paper: Lemma 8.2.0.3, p. 385. The S-local norm-one orbit union is paracompact. -/
theorem sAdeleNormOneOrbitUnion_paracompactSpace :
    ParacompactSpace (sAdeleNormOneOrbitUnion F S) := by
  have h1 := sAdeleNormOneOrbitUnion_t2Space F S
  have h2 := sAdeleNormOneOrbitUnion_locallyCompactSpace F S
  have h3 := sAdeleNormOneOrbitUnion_sigmaCompactSpace F S
  infer_instance

/-- Paper: Lemma 8.2.0.3, p. 385. The global norm-one orbit union is paracompact. -/
theorem adeleNormOneOrbitUnion_paracompactSpace : ParacompactSpace (adeleNormOneOrbitUnion F) := by
  sorry

/-- Paper: Proposition 8.2.0.4, p. 386. The subgroup of global ideles obtained by
inserting the units of the local valuation ring at the specified finite place. -/
def embeddedFiniteLocalUnits (v : HeightOneSpectrum (𝓞 F)) : Subgroup 𝔸[F]ˣ :=
  ((IdeleGroup.ofAdicCompletion (𝓞 F) F v).comp
    (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom)).range

/-- Paper: Proposition 8.2.0.4, p. 386. The inserted local units have norm one at
the specified place and value one at all other places. -/
theorem mem_embeddedFiniteLocalUnits_iff (v : HeightOneSpectrum (𝓞 F)) (g : 𝔸[F]ˣ) :
    g ∈ embeddedFiniteLocalUnits F v ↔
      g.val.1 = 1 ∧ ‖g.val.2 v‖ = 1 ∧
        ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → g.val.2 w = 1 := by
  classical
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨?_, ?_, fun w hw => ?_⟩
    · change (AdeleRing.ofAdicCompletion (𝓞 F) F v
        (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u).val).1 = 1
      rw [AdeleRing.ofAdicCompletion_apply]
    · have h := FiniteAdeleRing.ofAdicCompletion_apply_coe F v
        (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u).val v
      have hval := h.trans (Pi.mulSingle_eq_same v _)
      refine (congrArg norm hval).trans ?_
      rw [Valued.toNormedField.norm_eq_one_iff]
      exact (HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one
        (K := F) (v := v)).mp u.isUnit
    · exact (FiniteAdeleRing.ofAdicCompletion_apply_coe F v
        (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u).val w).trans
        (Pi.mulSingle_eq_of_ne (i := v) (i' := w) hw _)
  · rintro ⟨h1, h2, h3⟩
    let x : v.adicCompletion F := g.val.2 v
    have hxval : Valued.v x = 1 := Valued.toNormedField.norm_eq_one_iff.mp h2
    have hxne : x ≠ 0 :=
      (Valuation.ne_zero_iff Valued.v).mp (by rw [hxval]; exact one_ne_zero)
    have hxm : x ∈ v.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, hxval]
    have hxim : x⁻¹ ∈ v.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hxval, inv_one]
    let u : (v.adicCompletionIntegers F)ˣ :=
      Units.mk ⟨x, hxm⟩ ⟨x⁻¹, hxim⟩
        (Subtype.ext (mul_inv_cancel₀ hxne)) (Subtype.ext (inv_mul_cancel₀ hxne))
    refine ⟨u, Units.ext (Prod.ext ?_ (FiniteAdeleRing.ext F fun w => ?_))⟩
    · change (AdeleRing.ofAdicCompletion (𝓞 F) F v
        (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u).val).1 = g.val.1
      rw [AdeleRing.ofAdicCompletion_apply, h1]
    · refine (FiniteAdeleRing.ofAdicCompletion_apply_coe F v
        (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u).val w).trans ?_
      obtain rfl | hw := eq_or_ne w v
      · exact Pi.mulSingle_eq_same _ _
      · rw [Pi.mulSingle_eq_of_ne hw, h3 w hw]

/-- Paper: Equation (8.2.0.9), p. 386. The S-local section at a finite place takes
parameters in the half-open interval from 1 to the absolute prime ideal norm. -/
def sAdeleFiniteOrbitSection (v : S) (τ : ℝ≥0ˣ →* 𝕀ₛ) : Set Aₛ :=
  (fun t : ℝ≥0ˣ ↦ τ t • sAdeleOrbitBasepoint F S (some (.inr v))) ''
    {t | t.val ∈ Set.Ico 1 (v.val.asIdeal.absNorm : ℝ≥0)}

/-- Paper: Equation (8.2.0.9), p. 386. The included left endpoint gives the S-local
single-zero base point. -/
theorem sAdeleOrbitBasepoint_mem_finiteOrbitSection (v : S) (τ : ℝ≥0ˣ →* 𝕀ₛ) :
    sAdeleOrbitBasepoint F S (some (.inr v)) ∈ sAdeleFiniteOrbitSection F S v τ := by
  sorry

/-- Paper: Equation (8.2.0.10), p. 386. The global section at a finite place takes
parameters in the half-open interval from 1 to the absolute prime ideal norm. -/
def adeleFiniteOrbitSection (v : HeightOneSpectrum (𝓞 F)) (τ : ℝ≥0ˣ →* 𝔸[F]ˣ) :
    Set 𝔸[F] :=
  (fun t : ℝ≥0ˣ ↦ τ t • adeleOrbitBasepoint F (some (.inr v))) ''
    {t | t.val ∈ Set.Ico 1 (v.asIdeal.absNorm : ℝ≥0)}

/-- Paper: Equation (8.2.0.10), p. 386. The included left endpoint gives the global
single-zero base point. -/
theorem adeleOrbitBasepoint_mem_finiteOrbitSection (v : HeightOneSpectrum (𝓞 F))
    (τ : ℝ≥0ˣ →* 𝔸[F]ˣ) :
    adeleOrbitBasepoint F (some (.inr v)) ∈ adeleFiniteOrbitSection F v τ := by
  sorry

/-- A uniformizer at a finite place, as a unit, with norm the reciprocal of the absolute norm. -/
private theorem sAdeleFiniteOrbit_transporter_uniformizer (v : HeightOneSpectrum (𝓞 F)) :
    ∃ π : (v.adicCompletion F)ˣ, ‖(π : v.adicCompletion F)‖ = (v.asIdeal.absNorm : ℝ)⁻¹ := by
  let val : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
  obtain ⟨π, hπ⟩ := val.exists_isUniformizer_of_isCyclic_of_nontrivial
  exact ⟨Units.mk0 (π : v.adicCompletion F) hπ.ne_zero, norm_uniformizer_adicCompletion v _ hπ⟩

/-- The norm of a unit at a finite place is an integer power of the absolute norm. -/
private theorem sAdeleFiniteOrbit_transporter_norm_zpow (v : HeightOneSpectrum (𝓞 F))
    (y : (v.adicCompletion F)ˣ) :
    ∃ m : ℤ, ‖(y : v.adicCompletion F)‖ = (v.asIdeal.absNorm : ℝ) ^ m := by
  obtain ⟨π, hπ⟩ := sAdeleFiniteOrbit_transporter_uniformizer F v
  obtain ⟨e, he1, he2⟩ := finitePlace_unitDecomposition v π hπ
  let ι := Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom
  have hy : y = π ^ (e y).1.toAdd * ι (e y).2 := by
    apply e.injective
    rw [map_mul, map_zpow, he1, he2]
    apply Prod.ext
    · show (e y).1 = Multiplicative.ofAdd (1 : ℤ) ^ (e y).1.toAdd * 1
      rw [mul_one, ← ofAdd_zsmul, smul_eq_mul, mul_one, ofAdd_toAdd]
    · simp
  obtain ⟨m, u, hmu⟩ : ∃ (m : ℤ) (u : (v.adicCompletionIntegers F)ˣ), y = π ^ m * ι u :=
    ⟨_, _, hy⟩
  refine ⟨-m, ?_⟩
  have hu : ‖((ι u : (v.adicCompletion F)ˣ) : v.adicCompletion F)‖ = 1 := by
    rw [Valued.toNormedField.norm_eq_one_iff]
    exact (HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one
      (K := F) (v := v)).mp u.isUnit
  rw [hmu, Units.val_mul, norm_mul, Units.val_zpow_eq_zpow_val, norm_zpow, hπ, hu, mul_one,
    inv_zpow, zpow_neg]

/-- The idele inserted at a finite place has the norm of the inserted unit. -/
private theorem sAdeleFiniteOrbit_transporter_ideleNorm (v : HeightOneSpectrum (𝓞 F))
    (w : (v.adicCompletion F)ˣ) :
    ((ideleNorm F (IdeleGroup.ofAdicCompletion (𝓞 F) F v w) : ℝ≥0) : ℝ) =
      ‖(w : v.adicCompletion F)‖ := by
  classical
  rw [((ideleNorm_spec F).1 _).2]
  change (∏ u : InfinitePlace F, ‖(1 : u.Completion)‖ ^ u.mult) *
    (∏ᶠ u : HeightOneSpectrum (𝓞 F), ‖FiniteAdeleRing.ofAdicCompletion F v w.val u‖) = _
  simp only [norm_one, one_pow, Finset.prod_const_one, one_mul]
  rw [finprod_eq_single _ v (fun u hu ↦ by
    rw [show FiniteAdeleRing.ofAdicCompletion F v w.val u = 1 from
      (FiniteAdeleRing.ofAdicCompletion_apply_coe F v _ u).trans (Pi.mulSingle_eq_of_ne hu _),
      norm_one])]
  rw [show FiniteAdeleRing.ofAdicCompletion F v w.val v = w.val from
    (FiniteAdeleRing.ofAdicCompletion_apply_coe F v _ v).trans (Pi.mulSingle_eq_same _ _)]

/-- Paper: Proposition 8.2.0.4(1), p. 386. Every point in the full S-local finite-place
orbit can be moved into the half-open section by a norm-one idele. The transporter
is unique up to the embedded local units.
Deviation: The transporter lies in the norm-one subgroup, correcting ERRATA R1. -/
theorem sAdeleFiniteOrbit_transporter (v : S) (τ : ℝ≥0ˣ →* 𝕀ₛ) (hτ : Continuous τ)
    (hsection : RightInverse τ (sIdeleNorm F S)) (x : Aₛ)
    (hx : x ∈ sAdeleFullOrbit F S (some (.inr v))) :
    ∃ g : Nₛ, g⁻¹ • x ∈ sAdeleFiniteOrbitSection F S v τ ∧
      ∀ h : Nₛ, h⁻¹ • x ∈ sAdeleFiniteOrbitSection F S v τ →
        g.val⁻¹ * h.val ∈ (embeddedFiniteLocalUnits F v.val).map
          (Units.map (adeleProjection F S).toMonoidHom) := by
  sorry

/-- A global idele fixes the base point at a finite place exactly when it is inserted
at that place. -/
private theorem adeleFiniteOrbit_transporter_smul (v : HeightOneSpectrum (𝓞 F)) (g : 𝔸[F]ˣ) :
    g • adeleOrbitBasepoint F (some (.inr v)) = adeleOrbitBasepoint F (some (.inr v)) ↔
      ∃ w : (v.adicCompletion F)ˣ, g = IdeleGroup.ofAdicCompletion (𝓞 F) F v w := by
  classical
  constructor
  · intro h
    rw [Units.smul_def] at h
    change g.val * AdeleRing.ofAdicCompletion (𝓞 F) F v 0 =
      AdeleRing.ofAdicCompletion (𝓞 F) F v 0 at h
    have h1 : g.val.1 = 1 := by
      have hc := congrArg Prod.fst h
      change g.val.1 * 1 = 1 at hc
      rwa [mul_one] at hc
    have h2 : ∀ w, w ≠ v → g.val.2 w = 1 := by
      intro w hw
      have hb : (AdeleRing.ofAdicCompletion (𝓞 F) F v 0).2 w = 1 :=
        (FiniteAdeleRing.ofAdicCompletion_apply_coe F v 0 w).trans (Pi.mulSingle_eq_of_ne hw _)
      have hc : g.val.2 w * (AdeleRing.ofAdicCompletion (𝓞 F) F v 0).2 w =
          (AdeleRing.ofAdicCompletion (𝓞 F) F v 0).2 w := congrArg (fun a : 𝔸[F] ↦ a.2 w) h
      rwa [hb, mul_one] at hc
    let u : (v.adicCompletion F)ˣ := ⟨g.val.2 v, g.inv.2 v,
      congrArg (fun a : 𝔸[F] ↦ a.2 v) g.val_inv, congrArg (fun a : 𝔸[F] ↦ a.2 v) g.inv_val⟩
    refine ⟨u, Units.ext (Prod.ext h1 (FiniteAdeleRing.ext F fun w ↦ ?_))⟩
    refine Eq.trans ?_ (FiniteAdeleRing.ofAdicCompletion_apply_coe F v (g.val.2 v) w).symm
    obtain rfl | hw := eq_or_ne w v
    · rw [Pi.mulSingle_eq_same]
    · rw [Pi.mulSingle_eq_of_ne hw, h2 w hw]
  · rintro ⟨u, rfl⟩
    rw [Units.smul_def]
    change AdeleRing.ofAdicCompletion (𝓞 F) F v u.val * AdeleRing.ofAdicCompletion (𝓞 F) F v 0 =
      AdeleRing.ofAdicCompletion (𝓞 F) F v 0
    rw [← map_mul, mul_zero]

/-- Two norm-one transporters into the half-open section differ by an embedded local unit. -/
private theorem adeleFiniteOrbit_transporter_unique (v : HeightOneSpectrum (𝓞 F))
    (τ : ℝ≥0ˣ →* 𝔸[F]ˣ) (hsection : RightInverse τ (ideleNorm F)) (x : 𝔸[F]) (g h : N₁)
    (hg : g⁻¹ • x ∈ adeleFiniteOrbitSection F v τ)
    (hh : h⁻¹ • x ∈ adeleFiniteOrbitSection F v τ) :
    g.val⁻¹ * h.val ∈ embeddedFiniteLocalUnits F v := by
  classical
  obtain ⟨t, ht, hgt⟩ := hg
  obtain ⟨t', ht', hht⟩ := hh
  dsimp only at hgt hht
  have e1 : (g.val * τ t) • adeleOrbitBasepoint F (some (.inr v)) = x := by
    rw [mul_smul]
    change g.val • (τ t • adeleOrbitBasepoint F (some (.inr v))) = x
    rw [hgt]
    exact smul_inv_smul g.val x
  have e2 : (h.val * τ t') • adeleOrbitBasepoint F (some (.inr v)) = x := by
    rw [mul_smul]
    change h.val • (τ t' • adeleOrbitBasepoint F (some (.inr v))) = x
    rw [hht]
    exact smul_inv_smul h.val x
  have hfix : ((g.val * τ t)⁻¹ * (h.val * τ t')) • adeleOrbitBasepoint F (some (.inr v)) =
      adeleOrbitBasepoint F (some (.inr v)) := by
    rw [mul_smul, e2, ← e1, inv_smul_smul]
  obtain ⟨w, hw⟩ := (adeleFiniteOrbit_transporter_smul F v _).mp hfix
  have hgn : ideleNorm F g.val = 1 := g.prop
  have hhn : ideleNorm F h.val = 1 := h.prop
  have hN : ideleNorm F (IdeleGroup.ofAdicCompletion (𝓞 F) F v w) = t⁻¹ * t' := by
    rw [← hw, map_mul, map_inv, map_mul, map_mul, hgn, hhn, hsection t, hsection t', one_mul,
      one_mul]
  have hwn : ‖(w : v.adicCompletion F)‖ = ((t' : ℝ≥0) : ℝ) / ((t : ℝ≥0) : ℝ) := by
    rw [← sAdeleFiniteOrbit_transporter_ideleNorm F v w, hN, Units.val_mul,
      Units.val_inv_eq_inv_val, NNReal.coe_mul, NNReal.coe_inv, inv_mul_eq_div]
  have hq : (1 : ℝ) < v.asIdeal.absNorm := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hq0 : (0 : ℝ) < v.asIdeal.absNorm := by linarith
  have ha1 : (1 : ℝ) ≤ ((t : ℝ≥0) : ℝ) := by exact_mod_cast ht.1
  have ha2 : ((t : ℝ≥0) : ℝ) < v.asIdeal.absNorm := by exact_mod_cast ht.2
  have hb1 : (1 : ℝ) ≤ ((t' : ℝ≥0) : ℝ) := by exact_mod_cast ht'.1
  have hb2 : ((t' : ℝ≥0) : ℝ) < v.asIdeal.absNorm := by exact_mod_cast ht'.2
  have ha0 : (0 : ℝ) < ((t : ℝ≥0) : ℝ) := by linarith
  obtain ⟨m, hm⟩ := sAdeleFiniteOrbit_transporter_norm_zpow F v w
  have hm0 : m = 0 := by
    rcases lt_trichotomy m 0 with hlt | heq | hgt'
    · exfalso
      have h1 : (v.asIdeal.absNorm : ℝ) ^ m ≤ (v.asIdeal.absNorm : ℝ) ^ (-1 : ℤ) :=
        zpow_le_zpow_right₀ hq.le (by omega)
      rw [zpow_neg_one] at h1
      have h2 : (v.asIdeal.absNorm : ℝ)⁻¹ < ((t' : ℝ≥0) : ℝ) / ((t : ℝ≥0) : ℝ) :=
        calc (v.asIdeal.absNorm : ℝ)⁻¹ = 1 / (v.asIdeal.absNorm : ℝ) := (one_div _).symm
          _ < 1 / ((t : ℝ≥0) : ℝ) := one_div_lt_one_div_of_lt ha0 ha2
          _ ≤ ((t' : ℝ≥0) : ℝ) / ((t : ℝ≥0) : ℝ) := div_le_div_of_nonneg_right hb1 ha0.le
      rw [← hwn, hm] at h2
      linarith
    · exact heq
    · exfalso
      have h1 : (v.asIdeal.absNorm : ℝ) ^ (1 : ℤ) ≤ (v.asIdeal.absNorm : ℝ) ^ m :=
        zpow_le_zpow_right₀ hq.le (by omega)
      rw [zpow_one] at h1
      have h2 : ((t' : ℝ≥0) : ℝ) / ((t : ℝ≥0) : ℝ) < v.asIdeal.absNorm :=
        lt_of_le_of_lt (div_le_self (by linarith) ha1) hb2
      rw [← hwn, hm] at h2
      linarith
  have hw1 : ‖(w : v.adicCompletion F)‖ = 1 := by rw [hm, hm0, zpow_zero]
  have htt : t' = t := by
    rw [hwn, div_eq_one_iff_eq ha0.ne'] at hw1
    exact Units.ext (NNReal.eq hw1)
  subst htt
  have hgh : g.val⁻¹ * h.val = IdeleGroup.ofAdicCompletion (𝓞 F) F v w := by
    rw [← hw, mul_inv, mul_mul_mul_comm, inv_mul_cancel, mul_one]
  rw [hgh, mem_embeddedFiniteLocalUnits_iff]
  refine ⟨rfl, ?_, fun w' hw' ↦ ?_⟩
  · rw [show (IdeleGroup.ofAdicCompletion (𝓞 F) F v w).val.2 v = w.val from
      (FiniteAdeleRing.ofAdicCompletion_apply_coe F v _ v).trans (Pi.mulSingle_eq_same _ _)]
    exact hw1
  · exact (FiniteAdeleRing.ofAdicCompletion_apply_coe F v _ w').trans
      (Pi.mulSingle_eq_of_ne hw' _)

/-- Every point of the full orbit has a norm-one transporter into the half-open section. -/
private theorem adeleFiniteOrbit_transporter_exists (v : HeightOneSpectrum (𝓞 F))
    (τ : ℝ≥0ˣ →* 𝔸[F]ˣ) (hsection : RightInverse τ (ideleNorm F)) (x : 𝔸[F])
    (hx : x ∈ adeleFullOrbit F (some (.inr v))) :
    ∃ g : N₁, g⁻¹ • x ∈ adeleFiniteOrbitSection F v τ := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨π, hπ⟩ := sAdeleFiniteOrbit_transporter_uniformizer F v
  have hq : (1 : ℝ) < v.asIdeal.absNorm := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hq0 : (0 : ℝ) < v.asIdeal.absNorm := by linarith
  obtain ⟨j, hj⟩ := exists_mem_Ico_zpow (x := ((ideleNorm F a : ℝ≥0) : ℝ))
    (y := (v.asIdeal.absNorm : ℝ))
    (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (ideleNorm F a).ne_zero)) hq
  let s := IdeleGroup.ofAdicCompletion (𝓞 F) F v (π ^ j)
  let t := ideleNorm F (a * s)
  have hs : s⁻¹ • adeleOrbitBasepoint F (some (.inr v)) = adeleOrbitBasepoint F (some (.inr v)) :=
    (adeleFiniteOrbit_transporter_smul F v s⁻¹).mpr ⟨(π ^ j)⁻¹, by rw [map_inv]⟩
  refine ⟨⟨a * s * (τ t)⁻¹, ?_⟩, t, ?_, ?_⟩
  · rw [MonoidHom.mem_ker, map_mul, map_inv, hsection t]
    exact mul_inv_cancel _
  · have htv : ((t : ℝ≥0) : ℝ) =
        ((ideleNorm F a : ℝ≥0) : ℝ) * (v.asIdeal.absNorm : ℝ) ^ (-j) := by
      change ((ideleNorm F (a * s) : ℝ≥0) : ℝ) = _
      rw [map_mul, Units.val_mul, NNReal.coe_mul, sAdeleFiniteOrbit_transporter_ideleNorm,
        Units.val_zpow_eq_zpow_val, norm_zpow, hπ, inv_zpow, zpow_neg]
    change (t : ℝ≥0) ∈ Set.Ico 1 (v.asIdeal.absNorm : ℝ≥0)
    rw [Set.mem_Ico, ← NNReal.coe_le_coe, ← NNReal.coe_lt_coe, htv, NNReal.coe_one,
      NNReal.coe_natCast, zpow_neg, ← div_eq_mul_inv]
    constructor
    · rw [le_div_iff₀ (zpow_pos hq0 j), one_mul]
      exact hj.1
    · rw [div_lt_iff₀ (zpow_pos hq0 j), mul_comm, ← zpow_add_one₀ hq0.ne']
      exact hj.2
  · change τ t • adeleOrbitBasepoint F (some (.inr v)) =
      (a * s * (τ t)⁻¹)⁻¹ • a • adeleOrbitBasepoint F (some (.inr v))
    rw [← mul_smul, show (a * s * (τ t)⁻¹)⁻¹ * a = τ t * s⁻¹ by group, mul_smul, hs]

/-- Paper: Proposition 8.2.0.4(2), p. 386. Every point in the full global finite-place
orbit can be moved into the half-open section by a norm-one idele. The transporter
is unique up to the embedded local units.
Deviation: The transporter lies in the norm-one subgroup, correcting ERRATA R1. -/
theorem adeleFiniteOrbit_transporter (v : HeightOneSpectrum (𝓞 F)) (τ : ℝ≥0ˣ →* 𝔸[F]ˣ)
    (hτ : Continuous τ) (hsection : RightInverse τ (ideleNorm F)) (x : 𝔸[F])
    (hx : x ∈ adeleFullOrbit F (some (.inr v))) :
    ∃ g : N₁, g⁻¹ • x ∈ adeleFiniteOrbitSection F v τ ∧
      ∀ h : N₁, h⁻¹ • x ∈ adeleFiniteOrbitSection F v τ →
        g.val⁻¹ * h.val ∈ embeddedFiniteLocalUnits F v := by
  obtain ⟨g, hg⟩ := adeleFiniteOrbit_transporter_exists F v τ hsection x hx
  exact ⟨g, hg, fun h hh ↦ adeleFiniteOrbit_transporter_unique F v τ hsection x g h hg hh⟩

/-- Paper: Proposition 8.2.0.5, p. 386. At an infinite place the full S-local orbit is
already the norm-one orbit of the distinguished base point. -/
theorem sAdeleNormOneOrbit_infinite_eq_full (v : InfinitePlace F) :
    sAdeleNormOneOrbit F S (some (.inl v)) = sAdeleFullOrbit F S (some (.inl v)) := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g.val, rfl⟩
  · rintro ⟨g, rfl⟩
    let s := singlePlaceIdeleNormSection F v
    let p := Units.map (adeleProjection F S).toMonoidHom
    have hτ (t : ℝ≥0ˣ) : sIdeleNorm F S (p (s t)) = t := by
      let A := integralAdelesOutside F S
      have hmem (u : ℝ≥0ˣ) : (s u).val ∈ A := by
        change (s u).val ∈ integralAdelesOutside F S
        delta integralAdelesOutside
        rw [Subring.mem_iInf]
        intro w
        rw [Subring.mem_iInf]
        intro _
        exact (w.adicCompletionIntegers F).one_mem
      have ht : s t ∈ A.toSubmonoid.units :=
        ⟨hmem t, by
          change ((s t)⁻¹).val ∈ A
          rw [← map_inv]
          exact hmem t⁻¹⟩
      let g := A.toSubmonoid.unitsEquivUnitsType ⟨s t, ht⟩
      exact ((sIdeleNorm_spec F S).1 g).symm.trans
        (singlePlaceIdeleNormSection_rightInverse F v t)
    let c := p (s (sIdeleNorm F S g)⁻¹)
    have hfix : c • sAdeleOrbitBasepoint F S (some (.inl v)) =
        sAdeleOrbitBasepoint F S (some (.inl v)) := by
      rw [Units.smul_def]
      change adeleProjection F S (AdeleRing.ofCompletion (𝓞 F) F v
          (infinitePlaceRealPower F v (v.mult : ℝ)⁻¹ (sIdeleNorm F S g)⁻¹).val) *
          adeleProjection F S (AdeleRing.ofCompletion (𝓞 F) F v 0) =
        adeleProjection F S (AdeleRing.ofCompletion (𝓞 F) F v 0)
      rw [← map_mul, ← map_mul, mul_zero]
    refine ⟨⟨g * c, ?_⟩, ?_⟩
    · rw [MonoidHom.mem_ker, map_mul, hτ, mul_inv_cancel]
    · change (g * c) • sAdeleOrbitBasepoint F S (some (.inl v)) = g • _
      rw [mul_smul, hfix]

/-- Paper: Proposition 8.2.0.5, p. 386. At an infinite place the full global orbit is
already the norm-one orbit of the distinguished base point. -/
theorem adeleNormOneOrbit_infinite_eq_full (v : InfinitePlace F) :
    adeleNormOneOrbit F (some (.inl v)) = adeleFullOrbit F (some (.inl v)) := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g.val, rfl⟩
  · rintro ⟨g, rfl⟩
    let c := singlePlaceIdeleNormSection F v (ideleNorm F g)⁻¹
    have hc : ideleNorm F c = (ideleNorm F g)⁻¹ :=
      singlePlaceIdeleNormSection_rightInverse F v _
    have hfix : c • adeleOrbitBasepoint F (some (.inl v)) =
        adeleOrbitBasepoint F (some (.inl v)) := by
      rw [Units.smul_def]
      change AdeleRing.ofCompletion (𝓞 F) F v
          (infinitePlaceRealPower F v (v.mult : ℝ)⁻¹ (ideleNorm F g)⁻¹).val *
          AdeleRing.ofCompletion (𝓞 F) F v 0 = AdeleRing.ofCompletion (𝓞 F) F v 0
      rw [← map_mul, mul_zero]
    refine ⟨⟨g * c, ?_⟩, ?_⟩
    · rw [MonoidHom.mem_ker, map_mul, hc, mul_inv_cancel]
    · change (g * c) • adeleOrbitBasepoint F (some (.inl v)) = g • _
      rw [mul_smul, hfix]

/-- The idele inserted at an infinite place has norm one exactly when the inserted
unit has norm one. -/
private theorem sAdeleFullOrbit_real_normOne_stabilizer_iff_ideleNorm (v : InfinitePlace F)
    (u : v.Completionˣ) :
    ideleNorm F (IdeleGroup.ofCompletion (𝓞 F) F v u) = 1 ↔ ‖(u : v.Completion)‖ = 1 := by
  classical
  rw [Units.ext_iff, Units.val_one, ← NNReal.coe_eq_one, ((ideleNorm_spec F).1 _).2]
  change (∏ w : InfinitePlace F, ‖Pi.mulSingle v (u : v.Completion) w‖ ^ w.mult) *
    (∏ᶠ w : HeightOneSpectrum (𝓞 F), ‖(1 : w.adicCompletion F)‖) = 1 ↔ _
  simp only [norm_one, finprod_one, mul_one]
  rw [Finset.prod_eq_single_of_mem v (Finset.mem_univ _), Pi.mulSingle_eq_same]
  · exact pow_eq_one_iff_of_nonneg (norm_nonneg _) InfinitePlace.mult_pos.ne'
  · intro w _ hw
    simp only [Pi.mulSingle_eq_of_ne hw, norm_one, one_pow]

/-- At a real place the units of norm one are the two signs. -/
private theorem sAdeleFullOrbit_real_normOne_stabilizer_iff_unit (v : InfinitePlace F)
    (hv : v.IsReal) (u : v.Completionˣ) : ‖u.val‖ = 1 ↔ (u.val = 1 ∨ u.val = -1) := by
  let φ := InfinitePlace.Completion.extensionEmbeddingOfIsReal hv
  have hiso := InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv
  rw [← hiso.norm_map_of_map_zero (map_zero φ) u.val, Real.norm_eq_abs, abs_eq zero_le_one]
  constructor
  · rintro (h | h)
    · exact Or.inl (hiso.injective (h.trans (map_one φ).symm))
    · exact Or.inr (hiso.injective (h.trans (by rw [map_neg, map_one])))
  · rintro (h | h)
    · exact Or.inl (by rw [h, map_one])
    · exact Or.inr (by rw [h, map_neg, map_one])

/-- An S-idele fixes the S-local base point at an infinite place exactly when it is the
projection of an idele inserted at that place. -/
private theorem sAdeleFullOrbit_real_normOne_stabilizer_iff_smul (v : InfinitePlace F)
    (g : (SAdeleRing F S)ˣ) :
    g • sAdeleOrbitBasepoint F S (some (.inl v)) = sAdeleOrbitBasepoint F S (some (.inl v)) ↔
      ∃ u : v.Completionˣ, g = Units.map (adeleProjection F S).toMonoidHom
        (IdeleGroup.ofCompletion (𝓞 F) F v u) := by
  classical
  constructor
  · intro h
    rw [Units.smul_def] at h
    have h1 : ∀ w, w ≠ v → g.val.1 w = 1 := by
      intro w hw
      have hc := congrFun (congrArg Prod.fst h) w
      change g.val.1 w * Pi.mulSingle v 0 w = Pi.mulSingle v 0 w at hc
      rwa [Pi.mulSingle_eq_of_ne hw, mul_one] at hc
    have h2 : ∀ w : S, g.val.2 w = 1 := by
      intro w
      have hc := congrFun (congrArg Prod.snd h) w
      change g.val.2 w * 1 = 1 at hc
      rwa [mul_one] at hc
    let u : v.Completionˣ := ⟨g.val.1 v, g.inv.1 v, congrFun (congrArg Prod.fst g.val_inv) v,
      congrFun (congrArg Prod.fst g.inv_val) v⟩
    refine ⟨u, Units.ext (Prod.ext (funext fun w ↦ ?_) (funext fun w ↦ ?_))⟩
    · change g.val.1 w = Pi.mulSingle v (g.val.1 v) w
      obtain rfl | hw := eq_or_ne w v
      · rw [Pi.mulSingle_eq_same]
      · rw [Pi.mulSingle_eq_of_ne hw, h1 w hw]
    · change g.val.2 w = 1
      exact h2 w
  · rintro ⟨u, rfl⟩
    rw [Units.smul_def]
    change adeleProjection F S (AdeleRing.ofCompletion (𝓞 F) F v u.val) *
        adeleProjection F S (AdeleRing.ofCompletion (𝓞 F) F v 0) =
      adeleProjection F S (AdeleRing.ofCompletion (𝓞 F) F v 0)
    rw [← map_mul, ← map_mul, mul_zero]

/-- The projected idele inserted at an infinite place has S-norm one exactly when the
inserted unit has norm one. -/
private theorem sAdeleFullOrbit_real_normOne_stabilizer_iff_sIdeleNorm (v : InfinitePlace F)
    (u : v.Completionˣ) :
    sIdeleNorm F S (Units.map (adeleProjection F S).toMonoidHom
      (IdeleGroup.ofCompletion (𝓞 F) F v u)) = 1 ↔ ‖(u : v.Completion)‖ = 1 := by
  let A := integralAdelesOutside F S
  let s := IdeleGroup.ofCompletion (𝓞 F) F v
  have hmem (y : v.Completionˣ) : (s y).val ∈ A := by
    change (s y).val ∈ integralAdelesOutside F S
    delta integralAdelesOutside
    rw [Subring.mem_iInf]
    intro w
    rw [Subring.mem_iInf]
    intro _
    exact (w.adicCompletionIntegers F).one_mem
  have ht : s u ∈ A.toSubmonoid.units :=
    ⟨hmem u, by
      change ((s u)⁻¹).val ∈ A
      rw [← map_inv]
      exact hmem u⁻¹⟩
  let g := A.toSubmonoid.unitsEquivUnitsType ⟨s u, ht⟩
  have hg : sIdeleNorm F S (Units.map (adeleProjection F S).toMonoidHom (s u)) =
      ideleNorm F (s u) := ((sIdeleNorm_spec F S).1 g).symm
  rw [hg]
  exact sAdeleFullOrbit_real_normOne_stabilizer_iff_ideleNorm F v u

/-- At an infinite place the S-local norm-one stabilizer of an orbit point consists of
the projected ideles inserted at that place with a unit of norm one. -/
private theorem sAdeleFullOrbit_real_normOne_stabilizer_iff_aux (v : InfinitePlace F)
    (x : SAdeleRing F S) (hx : x ∈ sAdeleFullOrbit F S (some (.inl v)))
    (g : (SAdeleRing F S)ˣ) :
    (sIdeleNorm F S g = 1 ∧ g • x = x) ↔
      ∃ u : v.Completionˣ, ‖u.val‖ = 1 ∧
        g = Units.map (adeleProjection F S).toMonoidHom (IdeleGroup.ofCompletion (𝓞 F) F v u) := by
  obtain ⟨h, rfl⟩ := hx
  change sIdeleNorm F S g = 1 ∧ g • h • sAdeleOrbitBasepoint F S (some (.inl v)) =
    h • sAdeleOrbitBasepoint F S (some (.inl v)) ↔ _
  rw [← mul_smul, mul_comm g h, mul_smul, smul_left_cancel_iff,
    sAdeleFullOrbit_real_normOne_stabilizer_iff_smul]
  constructor
  · rintro ⟨hn, u, rfl⟩
    exact ⟨u, (sAdeleFullOrbit_real_normOne_stabilizer_iff_sIdeleNorm F S v u).mp hn, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨(sAdeleFullOrbit_real_normOne_stabilizer_iff_sIdeleNorm F S v u).mpr hu, u, rfl⟩

/-- Paper: Proposition 8.2.0.5(1), p. 386. At a real place the norm-one
stabilizer of every point of the S-local orbit is the image of the two local signs. -/
theorem sAdeleFullOrbit_real_normOne_stabilizer_iff (v : InfinitePlace F) (hv : v.IsReal)
    (x : Aₛ) (hx : x ∈ sAdeleFullOrbit F S (some (.inl v))) (g : 𝕀ₛ) :
    (sIdeleNorm F S g = 1 ∧ g • x = x) ↔
      ∃ u : v.Completionˣ, (u.val = 1 ∨ u.val = -1) ∧
        g = Units.map (adeleProjection F S).toMonoidHom (IdeleGroup.ofCompletion (𝓞 F) F v u) := by
  rw [sAdeleFullOrbit_real_normOne_stabilizer_iff_aux F S v x hx g]
  exact exists_congr fun u ↦
    and_congr (sAdeleFullOrbit_real_normOne_stabilizer_iff_unit F v hv u) Iff.rfl

/-- A global idele fixes the base point at an infinite place exactly when it is inserted
at that place. -/
private theorem adeleFullOrbit_real_normOne_stabilizer_iff_smul (v : InfinitePlace F)
    (g : 𝔸[F]ˣ) :
    g • adeleOrbitBasepoint F (some (.inl v)) = adeleOrbitBasepoint F (some (.inl v)) ↔
      ∃ u : v.Completionˣ, g = IdeleGroup.ofCompletion (𝓞 F) F v u := by
  classical
  constructor
  · intro h
    rw [Units.smul_def] at h
    change g.val * AdeleRing.ofCompletion (𝓞 F) F v 0 = AdeleRing.ofCompletion (𝓞 F) F v 0 at h
    have h1 : ∀ w, w ≠ v → g.val.1 w = 1 := by
      intro w hw
      have hc := congrFun (congrArg Prod.fst h) w
      change g.val.1 w * Pi.mulSingle v 0 w = Pi.mulSingle v 0 w at hc
      rwa [Pi.mulSingle_eq_of_ne hw, mul_one] at hc
    have h2 : g.val.2 = 1 := by
      have hc := congrArg Prod.snd h
      change g.val.2 * 1 = 1 at hc
      rwa [mul_one] at hc
    let u : v.Completionˣ := ⟨g.val.1 v, g.inv.1 v, congrFun (congrArg Prod.fst g.val_inv) v,
      congrFun (congrArg Prod.fst g.inv_val) v⟩
    refine ⟨u, Units.ext (Prod.ext (funext fun w ↦ ?_) h2)⟩
    change g.val.1 w = Pi.mulSingle v (g.val.1 v) w
    obtain rfl | hw := eq_or_ne w v
    · rw [Pi.mulSingle_eq_same]
    · rw [Pi.mulSingle_eq_of_ne hw, h1 w hw]
  · rintro ⟨u, rfl⟩
    rw [Units.smul_def]
    change AdeleRing.ofCompletion (𝓞 F) F v u.val * AdeleRing.ofCompletion (𝓞 F) F v 0 =
      AdeleRing.ofCompletion (𝓞 F) F v 0
    rw [← map_mul, mul_zero]

/-- At an infinite place the global norm-one stabilizer of an orbit point consists of
the ideles inserted at that place with a unit of norm one. -/
private theorem adeleFullOrbit_real_normOne_stabilizer_iff_aux (v : InfinitePlace F)
    (x : 𝔸[F]) (hx : x ∈ adeleFullOrbit F (some (.inl v))) (g : 𝔸[F]ˣ) :
    (ideleNorm F g = 1 ∧ g • x = x) ↔
      ∃ u : v.Completionˣ, ‖u.val‖ = 1 ∧ g = IdeleGroup.ofCompletion (𝓞 F) F v u := by
  obtain ⟨h, rfl⟩ := hx
  change ideleNorm F g = 1 ∧ g • h • adeleOrbitBasepoint F (some (.inl v)) =
    h • adeleOrbitBasepoint F (some (.inl v)) ↔ _
  rw [← mul_smul, mul_comm g h, mul_smul, smul_left_cancel_iff,
    adeleFullOrbit_real_normOne_stabilizer_iff_smul]
  constructor
  · rintro ⟨hn, u, rfl⟩
    exact ⟨u, (sAdeleFullOrbit_real_normOne_stabilizer_iff_ideleNorm F v u).mp hn, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨(sAdeleFullOrbit_real_normOne_stabilizer_iff_ideleNorm F v u).mpr hu, u, rfl⟩

/-- Paper: Proposition 8.2.0.5(1), p. 386. At a real place the norm-one
stabilizer of every point of the global orbit is the image of the two local signs. -/
theorem adeleFullOrbit_real_normOne_stabilizer_iff (v : InfinitePlace F) (hv : v.IsReal)
    (x : 𝔸[F]) (hx : x ∈ adeleFullOrbit F (some (.inl v))) (g : 𝔸[F]ˣ) :
    (ideleNorm F g = 1 ∧ g • x = x) ↔
      ∃ u : v.Completionˣ, (u.val = 1 ∨ u.val = -1) ∧
        g = IdeleGroup.ofCompletion (𝓞 F) F v u := by
  rw [adeleFullOrbit_real_normOne_stabilizer_iff_aux F v x hx g]
  exact exists_congr fun u ↦
    and_congr (sAdeleFullOrbit_real_normOne_stabilizer_iff_unit F v hv u) Iff.rfl

/-- Paper: Proposition 8.2.0.5(2), p. 387. At a complex place the norm-one
stabilizer of every point of the S-local orbit is the image of the local unit circle. -/
theorem sAdeleFullOrbit_complex_normOne_stabilizer_iff (v : InfinitePlace F) (hv : v.IsComplex)
    (x : Aₛ) (hx : x ∈ sAdeleFullOrbit F S (some (.inl v))) (g : 𝕀ₛ) :
    (sIdeleNorm F S g = 1 ∧ g • x = x) ↔
      ∃ u : v.Completionˣ, ‖u.val‖ = 1 ∧
        g = Units.map (adeleProjection F S).toMonoidHom (IdeleGroup.ofCompletion (𝓞 F) F v u) := by
  exact sAdeleFullOrbit_real_normOne_stabilizer_iff_aux F S v x hx g

/-- Paper: Proposition 8.2.0.5(2), p. 387. At a complex place the norm-one
stabilizer of every point of the global orbit is the image of the local unit circle. -/
theorem adeleFullOrbit_complex_normOne_stabilizer_iff (v : InfinitePlace F) (hv : v.IsComplex)
    (x : 𝔸[F]) (hx : x ∈ adeleFullOrbit F (some (.inl v))) (g : 𝔸[F]ˣ) :
    (ideleNorm F g = 1 ∧ g • x = x) ↔
      ∃ u : v.Completionˣ, ‖u.val‖ = 1 ∧
        g = IdeleGroup.ofCompletion (𝓞 F) F v u := by
  exact adeleFullOrbit_real_normOne_stabilizer_iff_aux F v x hx g

/-- Paper: Proposition 8.2.0.6(1), p. 387. The closure of the positive section ray
relative to the S-local full-orbit union adds the single-zero base point. -/
theorem sAdeleFullOrbitUnion_closure_sectionRay (v : InfinitePlace F) :
    let ray : Set Aₛ := Set.range fun t : ℝ≥0ˣ ↦
      adeleProjection F S (singlePlaceIdeleNormSection F v t).val
    closure ray ∩ sAdeleFullOrbitUnion F S =
      ray ∪ {sAdeleOrbitBasepoint F S (some (.inl v))} := by
  sorry

/-- Paper: Proposition 8.2.0.6(2), p. 387. The closure of the positive section ray
relative to the global full-orbit union adds the single-zero base point. -/
theorem adeleFullOrbitUnion_closure_sectionRay (v : InfinitePlace F) :
    let ray : Set 𝔸[F] := Set.range fun t : ℝ≥0ˣ ↦ (singlePlaceIdeleNormSection F v t).val
    closure ray ∩ adeleFullOrbitUnion F = ray ∪ {adeleOrbitBasepoint F (some (.inl v))} := by
  sorry

end RiemannMasullo
