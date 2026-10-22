/-
# Hypothetical Expected Utility: formalisation

Reference: E. Piermont, *Hypothetical Expected Utility*. This file proves

* Proposition `prop:closure`: `π` is coherent iff `Ω ∈ Π` and `π(H) = ⋂ {P ∈ Π | H ⊆ P}`;
* Lemma `lem:drvw`: an implication relation satisfies `(I1)`–`(I3)` iff it is interpreted by a
  unique coherent interpretation, namely `π(H) = ⋃ {G | G ⇒ H}`;
* Theorem `thm:dom`: a preorder satisfies `(A1)` iff its revealed implication is interpreted by a
  unique coherent interpretation;
* Theorem `thm:rep`: a preorder satisfies `(A1)`–`(A5)` iff it has an HEU representation `⟨π, μ⟩`;
  `π` is then unique, and `μ` is unique on `Π`.
-/

import Mathlib.Data.Set.Card
import Mathlib.Topology.Instances.NNReal.Lemmas

open Set Filter Topology
open scoped NNReal

namespace HEU

variable {Ω : Type*}

/-! ## Interpretations (§2.3) -/

/-- An *interpretation*: `π H` is the event the DM envisions given the hypothesis `H`. The paper's
`Π` is `range π`. -/
abbrev Interpretation (Ω : Type*) := Set Ω → Set Ω

namespace Interpretation

/-- Coherence: truth `(T)`, introspection `(I)` and monotonicity `(M)`. -/
structure IsCoherent (π : Interpretation Ω) : Prop where
  truth : ∀ H, H ⊆ π H
  introspection : ∀ H, π (π H) = π H
  mono : ∀ ⦃H G : Set Ω⦄, H ⊆ G → π H ⊆ π G

/-- `π` interprets the implication relation `imp` (eq. `(int)`): `H ⇒ G ↔ π(H) ⊆ π(G)`. -/
def Interprets (π : Interpretation Ω) (imp : Set Ω → Set Ω → Prop) : Prop :=
  ∀ H G, imp H G ↔ π H ⊆ π G

/-- **Proposition `prop:closure`.** `π` is coherent iff `Ω ∈ Π` and `(coh)` holds. Since
`⋂₀ ∅ = univ`, the conjunct `Ω ∈ Π` is not needed for the converse direction. -/
theorem isCoherent_iff {π : Interpretation Ω} :
    π.IsCoherent ↔ univ ∈ range π ∧ ∀ H, π H = ⋂₀ {P ∈ range π | H ⊆ P} := by
  constructor
  · intro hπ
    refine ⟨⟨univ, univ_subset_iff.1 (hπ.truth univ)⟩, fun H => ?_⟩
    refine (subset_sInter ?_).antisymm (sInter_subset_of_mem ⟨mem_range_self H, hπ.truth H⟩)
    rintro _ ⟨⟨G, rfl⟩, hHP⟩
    exact (hπ.mono hHP).trans (hπ.introspection G).subset
  · rintro ⟨-, h⟩
    have truth : ∀ H, H ⊆ π H := fun H => by rw [h H]; exact subset_sInter fun _ hP => hP.2
    refine ⟨truth, fun H => (?_ : π (π H) ⊆ π H).antisymm (truth _), fun H G hHG => ?_⟩
    · rw [h (π H)]; exact sInter_subset_of_mem ⟨mem_range_self H, Subset.rfl⟩
    · rw [h H, h G]; exact sInter_subset_sInter fun P hP => ⟨hP.1, hHG.trans hP.2⟩

end Interpretation

/-! ## Implication relations (Appendix, Lemma `lem:drvw`) -/

/-- An implication relation on events: `imp H G` reads "`H` implies `G`". -/
abbrev ImpRel (Ω : Type*) := Set Ω → Set Ω → Prop

namespace ImpRel

variable {imp : ImpRel Ω}

/-- Axioms `(I1)` transitivity, `(I2)` abstraction and `(I3)` monotonicity. -/
structure IsDeductive (imp : ImpRel Ω) : Prop where
  trans : ∀ ⦃H G F : Set Ω⦄, imp H G → imp G F → imp H F
  abstraction : ∀ ⦃H H' G : Set Ω⦄, imp H G → imp H' G → imp (H ∪ H') G
  mono : ∀ ⦃H G : Set Ω⦄, H ⊆ G → imp H G

/-- The canonical interpretation (eq. `(pi)`): `π(H) = ⋃ {G | G ⇒ H}`. -/
def interp (imp : ImpRel Ω) : Interpretation Ω := fun H => ⋃₀ {G | imp G H}

namespace IsDeductive

variable (hi : imp.IsDeductive)
include hi

/-- Iterated `(I2)`: a finite union of events each implying `H` implies `H`. -/
theorem sUnion_imp {S : Set (Set Ω)} (hS : S.Finite) {H : Set Ω} (h : ∀ G ∈ S, imp G H) :
    imp (⋃₀ S) H := by
  induction S, hS using Set.Finite.induction_on with
  | empty => rw [sUnion_empty]; exact hi.mono (empty_subset H)
  | @insert a s _ _ ih =>
    rw [sUnion_insert]
    exact hi.abstraction (h a (mem_insert a s)) (ih fun G hG => h G (mem_insert_of_mem a hG))

variable [Finite Ω]

/-- `G ⇒ H ↔ G ⊆ π(H)`, where `π` is the canonical interpretation. -/
theorem imp_iff {G H : Set Ω} : imp G H ↔ G ⊆ imp.interp H :=
  ⟨fun h => subset_sUnion_of_mem h,
   fun h => hi.trans (hi.mono h) (hi.sUnion_imp (toFinite _) fun _ hG => hG)⟩

/-- **Lemma `lem:drvw`**, sufficiency: the canonical interpretation is coherent. -/
theorem interp_isCoherent : imp.interp.IsCoherent where
  truth _ := hi.imp_iff.1 (hi.mono Subset.rfl)
  introspection _ :=
    (hi.imp_iff.1 (hi.trans (hi.imp_iff.2 Subset.rfl) (hi.imp_iff.2 Subset.rfl))).antisymm
      (hi.imp_iff.1 (hi.mono Subset.rfl))
  mono _ _ hHG := hi.imp_iff.1 (hi.trans (hi.imp_iff.2 Subset.rfl) (hi.mono hHG))

/-- **Lemma `lem:drvw`**, sufficiency: the canonical interpretation interprets `imp`. -/
theorem interp_interprets : imp.interp.Interprets imp := fun H _ =>
  ⟨fun h => hi.imp_iff.1 (hi.trans (hi.imp_iff.2 Subset.rfl) h),
   fun h => hi.imp_iff.2 ((hi.interp_isCoherent.truth H).trans h)⟩

end IsDeductive

end ImpRel

namespace Interpretation.IsCoherent

variable {π : Interpretation Ω} {imp : ImpRel Ω} (hπ : π.IsCoherent) (h : π.Interprets imp)
include hπ h

/-- **Lemma `lem:drvw`**, necessity. -/
theorem isDeductive : imp.IsDeductive where
  trans _ _ _ h₁ h₂ := (h _ _).2 (((h _ _).1 h₁).trans ((h _ _).1 h₂))
  abstraction H H' G h₁ h₂ := (h _ G).2 <|
    (hπ.mono (union_subset ((hπ.truth H).trans ((h H G).1 h₁))
      ((hπ.truth H').trans ((h H' G).1 h₂)))).trans (hπ.introspection G).subset
  mono _ _ hHG := (h _ _).2 (hπ.mono hHG)

/-- **Lemma `lem:drvw`**, uniqueness: `π` is the canonical interpretation (no finiteness needed). -/
theorem eq_interp : π = imp.interp := by
  funext H; ext ω
  rw [ImpRel.interp, mem_sUnion]
  exact ⟨fun hω => ⟨π H, (h _ H).2 (hπ.introspection H).subset, hω⟩,
    fun ⟨G, hG, hωG⟩ => (h G H).1 hG (hπ.truth G hωG)⟩

end Interpretation.IsCoherent

/-- **Lemma `lem:drvw`.** The unique interpretation is `imp.interp`, by `IsCoherent.eq_interp`. -/
theorem ImpRel.isDeductive_iff [Finite Ω] {imp : ImpRel Ω} :
    imp.IsDeductive ↔ ∃! π : Interpretation Ω, π.IsCoherent ∧ π.Interprets imp :=
  ⟨fun hi => ⟨imp.interp, ⟨hi.interp_isCoherent, hi.interp_interprets⟩,
      fun _ ⟨hπ, h⟩ => hπ.eq_interp h⟩,
   fun ⟨_, ⟨hπ, h⟩, _⟩ => hπ.isDeductive h⟩

/-! ## Acts, bets and level sets (§2.1) -/

/-- An act: a state-contingent payoff, in utils. -/
abbrev Act (Ω : Type*) := Ω → ℝ≥0

/-- The bet `x_H`: pays `x` on `H` and `0` elsewhere. The constant act `x` is `bet x univ`. -/
noncomputable def bet (x : ℝ≥0) (H : Set Ω) : Act Ω := H.indicator fun _ => x

/-- `𝓗(f)`: the hypotheses on which the payoffs of `f` depend, i.e. its non-null level sets. -/
def hyps (f : Act Ω) : Set (Set Ω) := {H | ∃ ω, 0 < f ω ∧ H = f ⁻¹' {f ω}}

section bet

variable {x y : ℝ≥0} {G H : Set Ω} {ω : Ω}

@[simp] theorem bet_of_mem (h : ω ∈ H) : bet x H ω = x := by simp [bet, h]

@[simp] theorem bet_of_notMem (h : ω ∉ H) : bet x H ω = 0 := by simp [bet, h]

@[simp] theorem bet_zero (H : Set Ω) : bet 0 H = 0 := by
  funext ω; by_cases h : ω ∈ H <;> simp [h]

@[simp] theorem bet_empty (x : ℝ≥0) : bet x (∅ : Set Ω) = 0 := by funext ω; simp

@[simp] theorem smul_bet (c : ℝ≥0) : c • bet x H = bet (c * x) H := by
  funext ω; by_cases h : ω ∈ H <;> simp [h]

@[simp] theorem bet_add : bet x H + bet y H = bet (x + y) H := by
  funext ω; by_cases h : ω ∈ H <;> simp [h]

theorem bet_preimage (hx : x ≠ 0) : bet x H ⁻¹' {x} = H := by
  ext ω; by_cases h : ω ∈ H <;> simp [h, hx.symm]

@[simp] theorem hyps_zero : hyps (0 : Act Ω) = ∅ :=
  eq_empty_of_forall_notMem fun _ ⟨_, h, _⟩ => lt_irrefl _ h

theorem hyps_bet : hyps (bet x H) ⊆ {H} := by
  rintro _ ⟨ω, hω, rfl⟩
  have hωH : ω ∈ H := by by_contra h; simp [h] at hω
  rw [bet_of_mem hωH] at hω ⊢
  exact bet_preimage hω.ne'

theorem hyps_bet_mono (hy : 0 < y) : hyps (bet x G) ⊆ hyps (bet y G) := by
  intro K hK
  obtain ⟨ω, hω, -⟩ := id hK
  have hωG : ω ∈ G := by by_contra h; simp [h] at hω
  rw [eq_of_mem_singleton (hyps_bet hK)]
  exact ⟨ω, by simpa [hωG] using hy, by rw [bet_of_mem hωG, bet_preimage hy.ne']⟩

/-- If `𝓗(k) ⊆ 𝓗(k')` and `k(ω) > 0`, then `k` and `k'` have the same level set through `ω`. -/
theorem level_eq_of_subset {k k' : Act Ω} (h : hyps k ⊆ hyps k') (hω : 0 < k ω) :
    k ⁻¹' {k ω} = k' ⁻¹' {k' ω} := by
  obtain ⟨ω', -, e⟩ := h ⟨ω, hω, rfl⟩
  have hmem : ω ∈ k ⁻¹' {k ω} := rfl
  rw [e] at hmem
  rw [show k' ω = k' ω' from hmem]; exact e

end bet

/-! ## The HEU value (§2.4) -/

section value

variable (π : Interpretation Ω) (μ : Set Ω → ℝ≥0)

/-- The HEU value `V(f) = ∑_{H ∈ 𝓗(f)} f(H) μ(π(H))` (eq. `(heu)`), with each `H ∈ 𝓗(f)` indexed
by the value `x = f(H)`, so that `H = f⁻¹(x)`; the term `x = 0` vanishes. -/
noncomputable def V [Fintype Ω] (f : Act Ω) : ℝ≥0 :=
  ∑ x ∈ Finset.univ.image f, x * μ (π (f ⁻¹' {x}))

/-- The weight `μ(π(L)) / |L|` of the state `ω`, where `L = f⁻¹(f(ω))` is its level set. -/
noncomputable def weight (f : Act Ω) (ω : Ω) : ℝ≥0 :=
  μ (π (f ⁻¹' {f ω})) / (f ⁻¹' {f ω}).ncard

variable {π μ} {x : ℝ≥0} {H : Set Ω}

variable [Fintype Ω]

/-- Per-state form of `V`, obtained by spreading each `f(H) μ(π(H))` evenly over `H`. -/
theorem V_eq (f : Act Ω) : V π μ f = ∑ ω, f ω * weight π μ f ω := by
  rw [V, eq_comm]
  refine (Finset.sum_comp (fun x => x * (μ (π (f ⁻¹' {x})) / (f ⁻¹' {x}).ncard)) f).trans
    (Finset.sum_congr rfl fun x hx => ?_)
  obtain ⟨ω, -, rfl⟩ := Finset.mem_image.1 hx
  have hc : (Finset.univ.filter fun a => f a = f ω).card = (f ⁻¹' {f ω}).ncard := by
    rw [← ncard_coe_finset]; congr 1; ext; simp
  have h0 : ((f ⁻¹' {f ω}).ncard : ℝ≥0) ≠ 0 :=
    Nat.cast_ne_zero.2 ((ncard_pos (toFinite (f ⁻¹' {f ω}))).2 ⟨ω, rfl⟩).ne'
  rw [hc, nsmul_eq_mul, mul_left_comm, mul_div_cancel₀ _ h0]

theorem V_zero : V π μ 0 = 0 := by simp [V_eq]

theorem V_bet_of_nonempty (hH : H.Nonempty) : V π μ (bet x H) = x * μ (π H) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [V_zero]
  rw [V, Finset.sum_eq_single x, bet_preimage hx]
  · rintro _ hy hyx
    obtain ⟨ω, -, rfl⟩ := Finset.mem_image.1 hy
    by_cases hω : ω ∈ H
    · exact absurd (bet_of_mem hω) hyx
    · rw [bet_of_notMem hω, zero_mul]
  · obtain ⟨ω, hω⟩ := hH
    exact fun h => absurd (Finset.mem_image.2 ⟨ω, Finset.mem_univ _, bet_of_mem hω⟩) h

end value

/-- `μ` is a *likelihood assessment* on `C ∋ ∅, Ω`: `μ(Ω) = 1`, `μ(∅) = 0`, `μ ≤ 1` on `C`, and
`A ⊊ B` implies `μ(A) < μ(B)` on `C`. The values of `μ` off `C` play no role. -/
structure IsLikelihood (C : Set (Set Ω)) (μ : Set Ω → ℝ≥0) : Prop where
  empty_mem : ∅ ∈ C
  univ_mem : univ ∈ C
  map_empty : μ ∅ = 0
  map_univ : μ univ = 1
  le_one : ∀ A ∈ C, μ A ≤ 1
  strictMono : ∀ A ∈ C, ∀ B ∈ C, A ⊂ B → μ A < μ B

/-! ## Preferences and revealed implication (§2.1–2.2) -/

/-- A preference over acts: a reflexive and transitive relation. -/
structure Preference (Ω : Type*) where
  /-- `rel f g`: `f` is weakly preferred to `g`. -/
  rel : Act Ω → Act Ω → Prop
  refl : ∀ f, rel f f
  trans : ∀ {f g h}, rel f g → rel g h → rel f h

namespace Preference

variable (P : Preference Ω)

/-- Indifference `∼`. -/
def Indiff (f g : Act Ω) : Prop := P.rel f g ∧ P.rel g f

/-- Strict preference `≻`. -/
def Strict (f g : Act Ω) : Prop := P.rel f g ∧ ¬ P.rel g f

/-- Revealed implication (eq. `(imp)`): `H ⇒ G` iff `1_G ∼ 1_{H ∪ G}`. -/
def revImp : ImpRel Ω := fun H G => P.Indiff (bet 1 G) (bet 1 (H ∪ G))

end Preference

@[inherit_doc] scoped notation:50 f:51 " ≿[" P "] " g:51 => Preference.rel P f g
@[inherit_doc] scoped notation:50 f:51 " ∼[" P "] " g:51 => Preference.Indiff P f g
@[inherit_doc] scoped notation:50 f:51 " ≻[" P "] " g:51 => Preference.Strict P f g
@[inherit_doc] scoped notation:50 H:51 " ⇒[" P "] " G:51 => Preference.revImp P H G

namespace Preference

section dom

variable {P : Preference Ω} {f g h : Act Ω}

theorem Indiff.rfl : f ∼[P] f := ⟨P.refl f, P.refl f⟩

theorem Indiff.symm (h₁ : f ∼[P] g) : g ∼[P] f := ⟨h₁.2, h₁.1⟩

theorem Indiff.trans (h₁ : f ∼[P] g) (h₂ : g ∼[P] h) : f ∼[P] h :=
  ⟨P.trans h₁.1 h₂.1, P.trans h₂.2 h₁.2⟩

instance (P : Preference Ω) : @Trans (Act Ω) (Act Ω) (Act Ω) P.Indiff P.Indiff P.Indiff :=
  ⟨Indiff.trans⟩

/-- **Axiom `(A1)` Modularity**: if `1_G ∼ 1_{G ∪ F}` then `1_{G ∪ H} ∼ 1_{G ∪ H ∪ F}`. -/
def Modularity (P : Preference Ω) : Prop :=
  ∀ G F H : Set Ω, bet 1 G ∼[P] bet 1 (G ∪ F) → bet 1 (G ∪ H) ∼[P] bet 1 (G ∪ H ∪ F)

theorem revImp_iff {F G : Set Ω} : F ⇒[P] G ↔ bet 1 G ∼[P] bet 1 (G ∪ F) := by
  rw [union_comm]; rfl

/-- `(I3)` for revealed implication, by reflexivity of `≿`. -/
theorem revImp_of_subset (P : Preference Ω) {F G : Set Ω} (h : F ⊆ G) : F ⇒[P] G := by
  rw [revImp_iff, union_eq_self_of_subset_right h]; exact Indiff.rfl

/-- `(A1)` is equivalent to `(I1)`–`(I3)` for revealed implication. No finiteness is needed. -/
theorem modularity_iff_isDeductive : P.Modularity ↔ P.revImp.IsDeductive := by
  -- `(A1)` reads: `F ⇒ G` implies `F ⇒ G ∪ H`.
  have A1 : P.Modularity ↔ ∀ G F H : Set Ω, F ⇒[P] G → F ⇒[P] (G ∪ H) := by
    simp only [Modularity, revImp_iff]
  rw [A1]
  refine ⟨fun hmod => ⟨fun H G F hHG hGF => ?_, fun H H' G hH hH' => ?_,
    fun _ _ h => P.revImp_of_subset h⟩,
    fun hd _ _ _ h => hd.trans h (hd.mono subset_union_left)⟩
  · -- `(I1)`
    change bet 1 F ∼[P] bet 1 (H ∪ F)
    calc bet 1 F ∼[P] bet 1 (G ∪ F) := hGF
      _ ∼[P] bet 1 (H ∪ (G ∪ F)) := hmod G H F hHG
      _ = bet 1 (G ∪ (F ∪ H)) := by congr 1; ext; simp only [mem_union]; tauto
      _ ∼[P] bet 1 (F ∪ H) := (hmod F G H hGF).symm
      _ = bet 1 (H ∪ F) := by rw [union_comm]
  · -- `(I2)`
    change bet 1 G ∼[P] bet 1 (H ∪ H' ∪ G)
    calc bet 1 G ∼[P] bet 1 (H ∪ G) := hH
      _ = bet 1 (G ∪ H) := by rw [union_comm]
      _ ∼[P] bet 1 (H' ∪ (G ∪ H)) := hmod G H' H hH'
      _ = bet 1 (H ∪ H' ∪ G) := by congr 1; ext; simp only [mem_union]; tauto

/-- **Theorem `thm:dom`.** A preorder satisfies `(A1)` iff its revealed implication is interpreted
by a (unique) coherent interpretation. -/
theorem modularity_iff [Finite Ω] :
    P.Modularity ↔ ∃! π : Interpretation Ω, π.IsCoherent ∧ π.Interprets P.revImp :=
  modularity_iff_isDeductive.trans ImpRel.isDeductive_iff

end dom

/-! ## Exact acts (§2.2) -/

section exact

variable (P : Preference Ω)

/-- `𝓔` is `≿`-exact: no non-empty hypothesis is revealed to imply two distinct members. -/
def IsExact (𝓔 : Set (Set Ω)) : Prop :=
  ∀ F ∈ 𝓔, ∀ G ∈ 𝓔, F ≠ G → ∀ H : Set Ω, H.Nonempty → H ⇒[P] F → ¬ H ⇒[P] G

/-- `𝓐^{ex}`: the exact acts, i.e. those `f` with `𝓗(f)` exact. -/
def exactActs : Set (Act Ω) := {f | P.IsExact (hyps f)}

/-- A collection `𝓐'` of acts is exact if `𝓗(𝓐') = ⋃_{f ∈ 𝓐'} 𝓗(f)` is exact. -/
def IsExactColl (A : Set (Act Ω)) : Prop := P.IsExact (⋃ f ∈ A, hyps f)

variable {P} {A : Set (Act Ω)} {𝓔 𝓔' : Set (Set Ω)} {f g k k' : Act Ω} {H : Set Ω} {ω : Ω}

theorem IsExact.mono (h : P.IsExact 𝓔') (h' : 𝓔 ⊆ 𝓔') : P.IsExact 𝓔 :=
  fun F hF G hG => h F (h' hF) G (h' hG)

theorem isExact_of_subset (P : Preference Ω) {E : Set Ω} (h : 𝓔 ⊆ {E}) : P.IsExact 𝓔 :=
  fun _ hF _ hG hne =>
    absurd ((eq_of_mem_singleton (h hF)).trans (eq_of_mem_singleton (h hG)).symm) hne

theorem IsExactColl.mem (hA : P.IsExactColl A) (hf : f ∈ A) : f ∈ P.exactActs :=
  IsExact.mono hA (subset_biUnion_of_mem hf)

theorem bet_mem_exactActs (P : Preference Ω) {x : ℝ≥0} : bet x H ∈ P.exactActs :=
  P.isExact_of_subset hyps_bet

theorem isExactColl_bets (P : Preference Ω) {a b c : ℝ≥0} :
    P.IsExactColl {bet a H, bet b H, bet c H} :=
  P.isExact_of_subset <| iUnion₂_subset fun k hk => by
    rcases hk with rfl | rfl | rfl <;> exact hyps_bet

/-- In an exact collection, two acts that pay positively at `ω` share the level set through `ω`. -/
theorem IsExactColl.level_eq (hA : P.IsExactColl A) (hk : k ∈ A) (hk' : k' ∈ A) (h : 0 < k ω)
    (h' : 0 < k' ω) : k ⁻¹' {k ω} = k' ⁻¹' {k' ω} := by
  by_contra hne
  have hω (j : Act Ω) : {ω} ⊆ j ⁻¹' {j ω} := singleton_subset_iff.2 rfl
  exact hA _ (mem_biUnion hk ⟨ω, h, rfl⟩) _ (mem_biUnion hk' ⟨ω, h', rfl⟩) hne _
    (singleton_nonempty ω) (P.revImp_of_subset (hω k)) (P.revImp_of_subset (hω k'))

/-- `V` is affine along mixtures within an exact collection. -/
theorem IsExactColl.V_mix [Fintype Ω] {π : Interpretation Ω} {μ : Set Ω → ℝ≥0} {a b : ℝ≥0}
    (hA : P.IsExactColl A) (hf : f ∈ A) (hg : g ∈ A) (hh : a • f + b • g ∈ A) :
    V π μ (a • f + b • g) = a * V π μ f + b * V π μ g := by
  simp only [V_eq, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ω _ => ?_
  have e : ∀ k ∈ A, ∀ c : ℝ≥0, c * k ω ≤ (a • f + b • g) ω →
      c * k ω * weight π μ (a • f + b • g) ω = c * (k ω * weight π μ k ω) := by
    intro k hk c hc
    rcases eq_zero_or_pos (c * k ω) with h0 | h0
    · rw [h0, zero_mul, ← mul_assoc, h0, zero_mul]
    · rw [weight, weight, hA.level_eq hh hk (h0.trans_le hc)
        (pos_iff_ne_zero.2 (right_ne_zero_of_mul h0.ne')), mul_assoc]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
  rw [add_mul, e f hf a le_self_add, e g hg b le_add_self]

end exact

/-! ## Theorem `thm:rep` (§3.2) -/

section rep

variable (P : Preference Ω)

/-- **Axiom `(A2)` Completeness**: `≿` is complete on `𝓐^{ex}`. -/
def Completeness : Prop := ∀ f ∈ P.exactActs, ∀ g ∈ P.exactActs, f ≿[P] g ∨ g ≿[P] f

/-- **Axiom `(A3)` Bet monotonicity**: `H ⊆ G ≠ ∅` and `x > y` imply `x_G ≻ y_H`. -/
def BetMono : Prop :=
  ∀ H G : Set Ω, H ⊆ G → G.Nonempty → ∀ x y : ℝ≥0, y < x → bet x G ≻[P] bet y H

/-- **Axiom `(A4)` Exact continuity**: if `fⁿ → f` (pointwise) and `𝓗(fⁿ) ↓ 𝓗(f)`, read as
`𝓗(f) ⊆ 𝓗(fⁿ⁺¹) ⊆ 𝓗(fⁿ)`, then `fⁿ ≿ g` for all `n` implies `f ≿ g`, and dually. -/
def ExactCont : Prop :=
  ∀ f ∈ P.exactActs, ∀ g ∈ P.exactActs, ∀ F : ℕ → Act Ω, (∀ n, F n ∈ P.exactActs) →
    Tendsto F atTop (𝓝 f) → Antitone (fun n => hyps (F n)) → (∀ n, hyps f ⊆ hyps (F n)) →
      ((∀ n, F n ≿[P] g) → f ≿[P] g) ∧ ((∀ n, g ≿[P] F n) → g ≿[P] f)

/-- **Axiom `(A5)` Exact independence**. -/
def ExactInd : Prop :=
  ∀ α : ℝ≥0, 0 < α → α < 1 → ∀ f g f' g' : Act Ω,
    P.IsExactColl {f, g, α • f + (1 - α) • g} → P.IsExactColl {f', g', α • f' + (1 - α) • g'} →
      f ∼[P] f' → g ∼[P] g' → α • f + (1 - α) • g ∼[P] α • f' + (1 - α) • g'

variable [Fintype Ω]

/-- An **HEU representation** `⟨π, μ⟩` of `≿`: `π` is a coherent interpretation of `≿`, `μ` is a
likelihood assessment on `Π`, and `(heu)` holds on `𝓐^{ex}`. -/
structure IsHEU (π : Interpretation Ω) (μ : Set Ω → ℝ≥0) : Prop where
  coherent : π.IsCoherent
  interprets : π.Interprets P.revImp
  likelihood : IsLikelihood (range π) μ
  rep : ∀ f ∈ P.exactActs, ∀ g ∈ P.exactActs, f ≿[P] g ↔ V π μ g ≤ V π μ f

variable {P} {π π' : Interpretation Ω} {μ μ' : Set Ω → ℝ≥0} {f g : Act Ω}

namespace IsHEU

variable (h : P.IsHEU π μ)
include h

theorem interp_empty : π ∅ = ∅ := by
  obtain ⟨K, hK⟩ := h.likelihood.empty_mem
  rw [← hK]; exact h.coherent.introspection K

theorem V_bet (x : ℝ≥0) (H : Set Ω) : V π μ (bet x H) = x * μ (π H) := by
  rcases H.eq_empty_or_nonempty with rfl | hH
  · rw [bet_empty, V_zero, h.interp_empty, h.likelihood.map_empty, mul_zero]
  · exact V_bet_of_nonempty hH

theorem indiff_iff (hf : f ∈ P.exactActs) (hg : g ∈ P.exactActs) :
    f ∼[P] g ↔ V π μ f = V π μ g := by
  rw [le_antisymm_iff, ← h.rep f hf g hg, ← h.rep g hg f hf, and_comm]; rfl

/-- **Theorem `thm:rep`**, "if": an HEU preference satisfies `(A1)`–`(A5)`. -/
theorem axioms : P.Modularity ∧ P.Completeness ∧ P.BetMono ∧ P.ExactCont ∧ P.ExactInd := by
  have hb {x : ℝ≥0} {H : Set Ω} : bet x H ∈ P.exactActs := P.bet_mem_exactActs
  refine ⟨modularity_iff_isDeductive.2 (h.coherent.isDeductive h.interprets),
    fun f hf g hg => (le_total (V π μ g) (V π μ f)).imp (h.rep f hf g hg).2 (h.rep g hg f hf).2,
    fun H G hHG hG x y hxy => ?_, fun f hf g hg F hF hlim hanti hsub => ?_,
    fun α _ _ f g f' g' hA hA' hff' hgg' => ?_⟩
  · -- `(A3)`: `V(y_H) = y μ(π(H)) ≤ y μ(π(G)) < x μ(π(G)) = V(x_G)`
    have hG0 : 0 < μ (π G) := h.likelihood.map_empty ▸ h.likelihood.strictMono _
      h.likelihood.empty_mem _ ⟨G, rfl⟩ (empty_ssubset.2 (hG.mono (h.coherent.truth G)))
    have hHG' : μ (π H) ≤ μ (π G) := (Set.eq_or_ssubset_of_subset (h.coherent.mono hHG)).elim
      (fun e => e ▸ le_rfl) fun hs => (h.likelihood.strictMono _ ⟨H, rfl⟩ _ ⟨G, rfl⟩ hs).le
    have key : V π μ (bet y H) < V π μ (bet x G) := by
      rw [h.V_bet, h.V_bet]
      exact (mul_le_mul_of_nonneg_left hHG' zero_le).trans_lt (mul_lt_mul_of_pos_right hxy hG0)
    exact ⟨(h.rep _ hb _ hb).2 key.le, fun h' => not_le.2 key ((h.rep _ hb _ hb).1 h')⟩
  · -- `(A4)`: each `F n`, and `f`, has its level sets among those of `F 0`, so all `V(F n)` and
    -- `V(f)` are sums against the same weights
    have e {k : Act Ω} (hk : hyps k ⊆ hyps (F 0)) : V π μ k = ∑ ω, k ω * weight π μ (F 0) ω := by
      refine (V_eq k).trans (Finset.sum_congr rfl fun ω _ => ?_)
      rcases eq_zero_or_pos (k ω) with h0 | h0
      · rw [h0, zero_mul, zero_mul]
      · rw [weight, weight, level_eq_of_subset hk h0]
    have hV : Tendsto (fun n => V π μ (F n)) atTop (𝓝 (V π μ f)) := by
      rw [e (hsub 0)]
      exact (tendsto_finsetSum _ fun ω _ => (tendsto_pi_nhds.1 hlim ω).mul_const _).congr
        fun n => (e (hanti (Nat.zero_le n))).symm
    exact ⟨fun h' => (h.rep f hf g hg).2 <|
        ge_of_tendsto' hV fun n => (h.rep _ (hF n) g hg).1 (h' n),
      fun h' => (h.rep g hg f hf).2 <| le_of_tendsto' hV fun n => (h.rep g hg _ (hF n)).1 (h' n)⟩
  · -- `(A5)`: `V` is affine along exact mixtures
    have mem {f g : Act Ω} (hA : P.IsExactColl {f, g, α • f + (1 - α) • g}) :
        f ∈ P.exactActs ∧ g ∈ P.exactActs ∧ α • f + (1 - α) • g ∈ P.exactActs :=
      ⟨hA.mem (by simp), hA.mem (by simp), hA.mem (by simp)⟩
    have hV {f g : Act Ω} (hA : P.IsExactColl {f, g, α • f + (1 - α) • g}) :
        V π μ (α • f + (1 - α) • g) = α * V π μ f + (1 - α) * V π μ g :=
      hA.V_mix (by simp) (by simp) (by simp)
    obtain ⟨hf, hg, hm⟩ := mem hA
    obtain ⟨hf', hg', hm'⟩ := mem hA'
    rw [h.indiff_iff hf hf'] at hff'
    rw [h.indiff_iff hg hg'] at hgg'
    rw [h.indiff_iff hm hm', hV hA, hV hA', hff', hgg']

end IsHEU

/-- **Theorem `thm:rep`**, "only if": under `(A1)`–`(A5)`, the canonical interpretation `(pi)`,
together with `μ(P)` the certainty equivalent of `1_P`, is an HEU representation. -/
theorem exists_isHEU [Nonempty Ω] (hmod : P.Modularity) (hord : P.Completeness)
    (hmono : P.BetMono) (hcont : P.ExactCont) (hind : P.ExactInd) :
    ∃ μ, P.IsHEU P.revImp.interp μ := by
  classical
  have hd := modularity_iff_isDeductive.1 hmod
  have hπ := hd.interp_isCoherent
  have hint := hd.interp_interprets
  set π := P.revImp.interp
  have hb {x : ℝ≥0} {H : Set Ω} : bet x H ∈ P.exactActs := P.bet_mem_exactActs
  -- `(A4)` for bets `x_G` with `x > 0`, all of which have `𝓗(x_G) = 𝓗(1_G)`
  have lim {G : Set Ω} {x : ℕ → ℝ≥0} {x₀ : ℝ≥0} {g : Act Ω} (hg : g ∈ P.exactActs)
      (hx : Tendsto x atTop (𝓝 x₀)) (hpos : ∀ n, 0 < x n) :
      ((∀ n, bet (x n) G ≿[P] g) → bet x₀ G ≿[P] g) ∧
        ((∀ n, g ≿[P] bet (x n) G) → g ≿[P] bet x₀ G) :=
    hcont _ hb g hg (fun n => bet (x n) G) (fun _ => hb)
      (tendsto_pi_nhds.2 fun ω => by by_cases hω : ω ∈ G <;> simp [hω, hx])
      (fun m _ _ => hyps_bet_mono (hpos m)) fun n => hyps_bet_mono (hpos n)
  -- weak bet monotonicity, from `(A3)` and `(A4)`
  have wmono {H G : Set Ω} {x y : ℝ≥0} (hHG : H ⊆ G) (hyx : y ≤ x) : bet x G ≿[P] bet y H := by
    rcases G.eq_empty_or_nonempty with rfl | hG
    · rw [subset_empty_iff.1 hHG, bet_empty, bet_empty]; exact P.refl _
    rcases hyx.lt_or_eq with hlt | hxy
    · exact (hmono H G hHG hG x y hlt).1
    · obtain ⟨u, -, hu, hlim⟩ := exists_seq_strictAnti_tendsto x
      exact (lim hb hlim fun n => zero_le.trans_lt (hu n)).1
        fun n => (hmono H G hHG hG _ y (hxy.trans_lt (hu n))).1
  have cle {x y : ℝ≥0} : bet x univ ≿[P] bet y univ ↔ y ≤ x :=
    ⟨fun h => not_lt.1 fun hxy => (hmono _ _ subset_rfl univ_nonempty y x hxy).2 h,
     fun h => wmono subset_rfl h⟩
  have ceq {x y : ℝ≥0} (h : bet x univ ∼[P] bet y univ) : x = y :=
    le_antisymm (cle.1 h.2) (cle.1 h.1)
  -- Lemma `lem:certequiv`: `y_H ∼ c` for `c = sup B`, `B = {c | y_H ≿ c}` (unique, by `ceq`)
  have ce (y : ℝ≥0) (H : Set Ω) : ∃ c, bet y H ∼[P] bet c univ := by
    set B := {c | bet y H ≿[P] bet c univ}
    have h0 : bet y H ≿[P] bet 0 univ := by simpa using wmono (empty_subset H) zero_le
    have hB : BddAbove B := ⟨y, fun c hc => not_lt.1 fun h =>
      (hmono _ _ (subset_univ H) univ_nonempty c y h).2 hc⟩
    refine ⟨sSup B, ?_, ?_⟩
    · -- approach `sup B` from below, within `B`
      rcases eq_zero_or_pos (sSup B) with h | h
      · rw [h]; exact h0
      obtain ⟨u, -, hu, hlim⟩ := exists_seq_strictMono_tendsto' h
      refine (lim hb hlim fun n => (hu n).1).2 fun n => ?_
      obtain ⟨c, hc, hlt⟩ := exists_lt_of_lt_csSup ⟨0, h0⟩ (hu n).2
      exact P.trans hc (wmono subset_rfl hlt.le)
    · -- approach `sup B` from above, outside `B`, where `(A2)` gives `c ≿ y_H`
      obtain ⟨v, -, hv, hlim⟩ := exists_seq_strictAnti_tendsto (sSup B)
      exact (lim hb hlim fun n => zero_le.trans_lt (hv n)).1 fun n =>
        (hord _ hb _ hb).resolve_right fun h => not_le.2 (hv n) (le_csSup hB h)
  choose μ hμ using ce 1
  -- `1_H ∼ 1_{π(H)} ∼ μ(π(H))`
  have h1 (H : Set Ω) : bet 1 H ∼[P] bet (μ (π H)) univ := by
    have e : π H ⇒[P] H := (hint _ _).2 (hπ.introspection H).subset
    rw [revImp_iff, union_eq_self_of_subset_left (hπ.truth H)] at e
    exact e.trans (hμ _)
  -- `(A5)` with `g = 0`: scaling a bet scales its certainty equivalent
  have down {t a b : ℝ≥0} {H : Set Ω} (ht0 : 0 < t) (ht1 : t < 1)
      (h : bet a H ∼[P] bet b univ) : bet (t * a) H ∼[P] bet (t * b) univ := by
    have := hind t ht0 ht1 (bet a H) (bet 0 H) (bet b univ) (bet 0 univ)
      (by simp only [smul_bet, bet_add]; exact P.isExactColl_bets)
      (by simp only [smul_bet, bet_add]; exact P.isExactColl_bets) h
      (by simp only [bet_zero]; exact Indiff.rfl)
    simpa using this
  -- base case of `(ce)`: `x_H ∼ x μ(π(H))`
  have hbet (x : ℝ≥0) (H : Set Ω) : bet x H ∼[P] bet (x * μ (π H)) univ := by
    rcases eq_zero_or_pos x with rfl | hx
    · simp only [bet_zero, zero_mul]; exact Indiff.rfl
    obtain ⟨c, hc⟩ := ce (x + 1) H
    have hM : (x + 1)⁻¹ * (x + 1) = 1 := inv_mul_cancel₀ (by positivity)
    have e1 := down (inv_pos.2 (by positivity)) (inv_lt_one_of_one_lt₀ (lt_add_of_pos_left 1 hx)) hc
    rw [hM] at e1
    have e2 : (x + 1)⁻¹ * c = μ (π H) := ceq (e1.symm.trans (h1 H))
    have e3 := down (t := x * (x + 1)⁻¹) (by positivity)
      (by rw [← div_eq_mul_inv, div_lt_one (by positivity)]; exact lt_add_one x) hc
    rwa [mul_assoc, hM, mul_one, mul_assoc, e2] at e3
  -- `(ce)`: `f ∼ V(f)` for exact `f`, by strong induction on (a superset of) the support of `f`
  have hV (f : Act Ω) (hf : f ∈ P.exactActs) : f ∼[P] bet (V π μ f) univ := by
    suffices ∀ (s : Finset Ω) (f : Act Ω), f ∈ P.exactActs → (∀ ω, 0 < f ω → ω ∈ s) →
        f ∼[P] bet (V π μ f) univ from this _ f hf fun ω _ => Finset.mem_univ ω
    intro s
    induction s using Finset.strongInduction
    rename_i s ih
    intro f hf hs
    by_cases h0 : ∀ ω, f ω = 0
    · obtain rfl : f = 0 := funext h0
      rw [V_zero, bet_zero]; exact Indiff.rfl
    obtain ⟨ω₀, hω₀⟩ := not_forall.1 h0
    replace hω₀ : 0 < f ω₀ := pos_iff_ne_zero.2 hω₀
    -- `f = ½ f^a + ½ f^b`: `f^a = 2f` on the level set `L ∋ ω₀`, `f^b = 2f` off it
    set L := f ⁻¹' {f ω₀}
    obtain ⟨fb, hfb⟩ : ∃ fb : Act Ω, fb = fun ω => if f ω = f ω₀ then 0 else 2 * f ω := ⟨_, rfl⟩
    have h12 : (1 : ℝ≥0) - 2⁻¹ = 2⁻¹ := tsub_eq_of_eq_add (by rw [← one_div, add_halves])
    have hf_eq : f = (2⁻¹ : ℝ≥0) • bet (2 * f ω₀) L + (1 - 2⁻¹ : ℝ≥0) • fb := by
      funext ω
      by_cases hω : f ω = f ω₀
      · simp [bet_of_mem (show ω ∈ L from hω), hfb, hω]
      · simp [bet_of_notMem (show ω ∉ L from hω), hfb, hω, h12]
    have hfb_hyps : hyps fb ⊆ hyps f := by
      rintro _ ⟨ω, hω, rfl⟩
      have hne : f ω ≠ f ω₀ := fun e => by simp [hfb, e] at hω
      have hfω : fb ω = 2 * f ω := by simp [hfb, hne]
      rw [hfω] at hω ⊢
      refine ⟨ω, pos_iff_ne_zero.2 fun e => by simp [e] at hω, ?_⟩
      ext ω'
      simp only [mem_preimage, mem_singleton_iff, hfb]
      split_ifs with h'
      · exact iff_of_false hω.ne fun e => hne (e ▸ h')
      · exact mul_right_inj' two_ne_zero
    have hA : P.IsExactColl {bet (2 * f ω₀) L, fb, f} := by
      refine IsExact.mono hf (iUnion₂_subset fun k hk => ?_)
      rcases hk with rfl | rfl | hk
      · exact hyps_bet.trans (singleton_subset_iff.2 ⟨ω₀, hω₀, rfl⟩)
      · exact hfb_hyps
      · simp [eq_of_mem_singleton hk]
    have iha : bet (2 * f ω₀) L ∼[P] bet (V π μ (bet (2 * f ω₀) L)) univ := by
      rw [V_bet_of_nonempty (H := L) ⟨ω₀, rfl⟩]; exact hbet _ _
    have ihb := ih (s.erase ω₀) (Finset.erase_ssubset (hs ω₀ hω₀)) fb (hA.mem (by simp))
      fun ω hω => by
        have hne : f ω ≠ f ω₀ := fun e => by simp [hfb, e] at hω
        exact Finset.mem_erase.2 ⟨fun e => hne (congrArg f e),
          hs ω (pos_iff_ne_zero.2 fun e => by simp [hfb, e] at hω)⟩
    have hVf : V π μ f = 2⁻¹ * V π μ (bet (2 * f ω₀) L) + (1 - 2⁻¹) * V π μ fb := by
      conv_lhs => rw [hf_eq]
      exact hA.V_mix (by simp) (by simp) (by rw [← hf_eq]; simp)
    have key := hind 2⁻¹ (by norm_num) (by norm_num) _ _ _ _ (by rw [← hf_eq]; exact hA)
      (by simp only [smul_bet, bet_add]; exact P.isExactColl_bets) iha ihb
    rw [← hf_eq, smul_bet, smul_bet, bet_add, ← hVf] at key
    exact key
  have hπ0 : π ∅ = ∅ := sUnion_eq_empty.2 fun G (hG : G ⇒[P] ∅) => by
    by_contra hne
    refine (hmono G G subset_rfl (nonempty_iff_ne_empty.2 hne) 1 0 one_pos).2 ?_
    rw [revImp_iff, bet_empty, empty_union] at hG
    rw [bet_zero]; exact hG.1
  refine ⟨μ, hπ, hint, ⟨⟨∅, hπ0⟩, ⟨univ, univ_subset_iff.1 (hπ.truth univ)⟩,
    ceq ((hμ ∅).symm.trans (by simp only [bet_empty, bet_zero]; exact Indiff.rfl)),
    (ceq (hμ univ)).symm, fun A _ => cle.1 (P.trans (wmono (subset_univ A) le_rfl) (hμ A).1),
    ?_⟩, fun f hf g hg => ?_⟩
  · -- strict monotonicity of `μ` on `Π`
    rintro _ ⟨A, rfl⟩ _ ⟨B, rfl⟩ hAB
    refine not_le.1 fun hle => hAB.2 ?_
    have e : π B ⇒[P] π A := by
      rw [revImp_iff, union_eq_self_of_subset_left hAB.1]
      exact ⟨P.trans (P.trans (hμ _).1 (cle.2 hle)) (hμ _).2, wmono hAB.1 le_rfl⟩
    simpa only [hπ.introspection] using (hint _ _).1 e
  · -- `(heu)`, from `(ce)`
    rw [← cle]
    exact ⟨fun h => P.trans (P.trans (hV f hf).2 h) (hV g hg).1,
      fun h => P.trans (P.trans (hV f hf).1 h) (hV g hg).2⟩

/-- **Theorem `thm:rep`.** `≿` satisfies `(A1)`–`(A5)` iff it has an HEU representation. -/
theorem heu_iff [Nonempty Ω] :
    P.Modularity ∧ P.Completeness ∧ P.BetMono ∧ P.ExactCont ∧ P.ExactInd ↔
      ∃ π μ, P.IsHEU π μ :=
  ⟨fun ⟨h1, h2, h3, h4, h5⟩ => ⟨_, exists_isHEU h1 h2 h3 h4 h5⟩, fun ⟨_, _, h⟩ => h.axioms⟩

/-- **Theorem `thm:rep`**, uniqueness: `π` is unique, and `μ` is unique on `Π`. -/
theorem IsHEU.unique (h : P.IsHEU π μ) (h' : P.IsHEU π' μ') : π = π' ∧ EqOn μ μ' (range π) := by
  obtain rfl := (h.coherent.eq_interp h.interprets).trans (h'.coherent.eq_interp h'.interprets).symm
  refine ⟨rfl, ?_⟩
  rintro _ ⟨H, rfl⟩
  -- under any representation `⟨π, ν⟩`, `ν(π(H))` is the certainty equivalent of `1_H`
  have e {ν : Set Ω → ℝ≥0} (hν : P.IsHEU π ν) : bet 1 H ∼[P] bet (ν (π H)) univ := by
    rw [hν.indiff_iff P.bet_mem_exactActs P.bet_mem_exactActs, hν.V_bet, hν.V_bet,
      univ_subset_iff.1 (hν.coherent.truth _), hν.likelihood.map_univ, one_mul, mul_one]
  have := (h.indiff_iff P.bet_mem_exactActs P.bet_mem_exactActs).1 ((e h).symm.trans (e h'))
  rwa [h.V_bet, h.V_bet, univ_subset_iff.1 (h.coherent.truth _), h.likelihood.map_univ, mul_one,
    mul_one] at this

end rep

end Preference

end HEU
