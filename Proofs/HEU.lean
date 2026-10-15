/-
# Hypothetical Expected Utility: formalisation

Reference: E. Piermont, *Hypothetical Expected Utility*.

This file currently covers

* the primitives of §3 (acts, bets, preferences, revealed implication `(imp)`, exactness);
* interpretations and coherence `(T)`, `(I)`, `(M)`, strong coherence `(D)`, the closure-operator
  characterisation of coherence stated in §3.3, and Lemmas `lem:pi` and `lem:charstar`;
* abstract implication relations, axioms `(I1)`–`(I3)`, and Lemma `lem:drvw`;
* **Theorem 1** (`thm:dom`): a preference satisfies `(A1)` modularity if and only if its revealed
  implication is interpreted by a unique coherent interpretation, together with the identification
  formula `π G = ⋃ {H | 1_G ∼ 1_{G ∪ H}}` stated after the theorem.

## Design

The development is layered so that later results can reuse each layer independently.

1. `Interpretation Ω := Set Ω → Set Ω`, with `Interpretation.IsCoherent` (a `Prop`-valued structure
   whose fields are the paper's `(T)`, `(I)`, `(M)`). `IsCoherent.toClosureOperator` transports a
   coherent interpretation to Mathlib's `ClosureOperator (Set Ω)`, so that the Mathlib API on closure
   operators is available.
2. `ImpRel Ω := Set Ω → Set Ω → Prop`, an abstract implication relation, with
   `ImpRel.IsDeductive` (axioms `(I1)`–`(I3)`), the canonical interpretation `ImpRel.interp`
   (eq. `(pi)`), and `Interpretation.Interprets` (eq. `(int)`). Lemma `lem:drvw` lives at this level and
   makes no reference to preferences.
3. `Act Ω := Ω → ℝ≥0`, bets `bet x H`, and `Preference Ω`, a bundled preorder on acts. The revealed
   implication `Preference.revImp` (eq. `(imp)`) is an `ImpRel Ω`, so every result of layer 2 applies to
   it directly. Preference axioms are stated as `Prop`-valued definitions in the `Preference`
   namespace (`Preference.Modularity` is `(A1)`).

Throughout, the state space is finite (`[Finite Ω]`) wherever this is used. It is needed only in the
sufficiency half of Lemma `lem:drvw`, where binary abstraction `(I2)` must be iterated over the
(finite) family `{G | G ⇒ H}`.

## Remark on the statement of Theorem 1

The paper states Theorem 1 for a *partial order* `≿`. The proof uses only reflexivity and transitivity,
and §3.1 assumes `≿` to be a preorder. Antisymmetry would in fact trivialise the revealed implication:
`1_G ∼ 1_{H ∪ G}` would force `1_G = 1_{H ∪ G}`, i.e. `H ⊆ G`. Accordingly `Preference` is a preorder.
-/
import Mathlib.Order.Closure
import Mathlib.Algebra.Notation.Indicator
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Basic.NNReal.Defs

open Set
open scoped NNReal

namespace HEU

variable {Ω : Type*}

/-! ## Interpretations (§3.3) -/

/-- An *interpretation*: `π H` is the event the DM envisions when the modeller describes the
hypothesis `H`. -/
abbrev Interpretation (Ω : Type*) := Set Ω → Set Ω

namespace Interpretation

variable (π : Interpretation Ω)

/-- `Π = {π H | H ⊆ Ω}`: the events the DM is able to conceive of. -/
def conceivable : Set (Set Ω) := range π

/-- A *coherent* interpretation satisfies truth `(T)`, introspection `(I)` and monotonicity `(M)`. -/
structure IsCoherent : Prop where
  /-- `(T)` Truth: `H ⊆ π(H)`. -/
  truth : ∀ H, H ⊆ π H
  /-- `(I)` Introspection: `π(π(H)) = π(H)`. -/
  introspection : ∀ H, π (π H) = π H
  /-- `(M)` Monotonicity: `H ⊆ G → π(H) ⊆ π(G)`. -/
  mono : ∀ ⦃H G : Set Ω⦄, H ⊆ G → π H ⊆ π G

/-- A *strongly coherent* interpretation satisfies `(T)`, `(I)` and distribution `(D)`. -/
structure IsStronglyCoherent : Prop where
  /-- `(T)` Truth. -/
  truth : ∀ H, H ⊆ π H
  /-- `(I)` Introspection. -/
  introspection : ∀ H, π (π H) = π H
  /-- `(D)` Distribution: `π(H ∪ G) = π(H) ∪ π(G)`. -/
  distrib : ∀ H G, π (H ∪ G) = π H ∪ π G

/-- `π` *interprets* the implication relation `imp` (eq. `(int)`): `H ⇒ G ↔ π(H) ⊆ π(G)`. -/
def Interprets (imp : Set Ω → Set Ω → Prop) : Prop :=
  ∀ H G, imp H G ↔ π H ⊆ π G

/-- The rational DM: the identity interpretation (`Π = 2^Ω`). -/
theorem isCoherent_id : IsCoherent (id : Interpretation Ω) :=
  ⟨fun _ => Subset.rfl, fun _ => rfl, fun _ _ h => h⟩

/-- The opposite extreme: no hypothesis is informative (`Π = {Ω}`). -/
theorem isCoherent_const_univ : IsCoherent (fun _ => univ : Interpretation Ω) :=
  ⟨fun _ => subset_univ _, fun _ => rfl, fun _ _ _ => Subset.rfl⟩

variable {π}

/-- `(D)` implies `(M)`. -/
theorem IsStronglyCoherent.mono (hπ : π.IsStronglyCoherent) ⦃H G : Set Ω⦄ (h : H ⊆ G) :
    π H ⊆ π G := by
  rw [← union_eq_self_of_subset_left h, hπ.distrib]
  exact subset_union_left

/-- A strongly coherent interpretation is coherent. -/
theorem IsStronglyCoherent.isCoherent (hπ : π.IsStronglyCoherent) : π.IsCoherent :=
  ⟨hπ.truth, hπ.introspection, hπ.mono⟩

namespace IsCoherent

variable (hπ : π.IsCoherent)
include hπ

theorem monotone : Monotone π := fun _ _ h => hπ.mono h

/-- A coherent interpretation, viewed as a closure operator on the lattice `Set Ω`. -/
def toClosureOperator : ClosureOperator (Set Ω) where
  toFun := π
  monotone' := hπ.monotone
  le_closure' := hπ.truth
  idempotent' := hπ.introspection

@[simp]
theorem coe_toClosureOperator : ⇑hπ.toClosureOperator = π := rfl

/-- **Lemma `lem:charstar`**, (1) ↔ (2): `π(H) ⊆ π(G) ↔ H ⊆ π(G)`. -/
theorem subset_iff {H G : Set Ω} : π H ⊆ π G ↔ H ⊆ π G :=
  ⟨fun h => (hπ.truth H).trans h, fun h =>
    calc π H ⊆ π (π G) := hπ.mono h
      _ = π G := hπ.introspection G⟩

/-- **Lemma `lem:charstar`**, (2) ↔ (3): `H ⊆ π(G) ↔ π(H ∪ G) = π(G)`. -/
theorem union_eq_iff {H G : Set Ω} : π (H ∪ G) = π G ↔ H ⊆ π G := by
  constructor
  · intro h
    calc H ⊆ H ∪ G := subset_union_left
      _ ⊆ π (H ∪ G) := hπ.truth _
      _ = π G := h
  · intro h
    refine Subset.antisymm ?_ (hπ.mono subset_union_right)
    exact hπ.subset_iff.2 (union_subset h (hπ.truth G))

/-- A conceivable event is a fixed point of `π`. -/
theorem mem_conceivable_iff {P : Set Ω} : P ∈ π.conceivable ↔ π P = P :=
  ⟨by rintro ⟨H, rfl⟩; exact hπ.introspection H, fun h => ⟨P, h⟩⟩

theorem univ_mem_conceivable : (univ : Set Ω) ∈ π.conceivable :=
  ⟨univ, univ_subset_iff.1 (hπ.truth univ)⟩

/-- **Lemma `lem:pi`**: `Π` is closed under arbitrary intersections. -/
theorem sInter_mem_conceivable {S : Set (Set Ω)} (hS : S ⊆ π.conceivable) :
    ⋂₀ S ∈ π.conceivable := by
  rw [hπ.mem_conceivable_iff]
  refine Subset.antisymm (subset_sInter fun P hP => ?_) (hπ.truth _)
  calc π (⋂₀ S) ⊆ π P := hπ.mono (sInter_subset_of_mem hP)
    _ = P := hπ.mem_conceivable_iff.1 (hS hP)

end IsCoherent

/-- A closure operator on `Set Ω` is a coherent interpretation. -/
theorem _root_.ClosureOperator.isCoherent (c : ClosureOperator (Set Ω)) :
    Interpretation.IsCoherent (⇑c) :=
  ⟨c.le_closure, c.idempotent, fun _ _ h => c.monotone h⟩

/-- **Characterisation of coherence (§3.3).** `π` is coherent iff
`π(H) = ⋂ {P ∈ Π | H ⊆ P}` for every `H`. By `IsCoherent.univ_mem_conceivable` and
`IsCoherent.sInter_mem_conceivable`, `Π` then contains `Ω` and is closed under intersections; these two
closure properties are consequences of the displayed identity rather than additional hypotheses. -/
theorem isCoherent_iff_eq_sInter :
    π.IsCoherent ↔ ∀ H, π H = ⋂₀ {P | P ∈ π.conceivable ∧ H ⊆ P} := by
  constructor
  · intro hπ H
    refine Subset.antisymm (subset_sInter ?_) (sInter_subset_of_mem ⟨⟨H, rfl⟩, hπ.truth H⟩)
    rintro P ⟨hP, hHP⟩
    calc π H ⊆ π P := hπ.mono hHP
      _ = P := hπ.mem_conceivable_iff.1 hP
  · intro h
    have truth : ∀ H, H ⊆ π H := fun H => by
      rw [h H]
      exact subset_sInter fun P hP => hP.2
    refine ⟨truth, fun H => Subset.antisymm ?_ (truth _), fun H G hHG => ?_⟩
    · rw [h (π H)]
      exact sInter_subset_of_mem ⟨⟨H, rfl⟩, Subset.rfl⟩
    · rw [h H, h G]
      exact sInter_subset_sInter fun P hP => ⟨hP.1, hHG.trans hP.2⟩

end Interpretation

/-! ## Implication relations (Appendix B.2) -/

/-- An (abstract) implication relation on events: `imp H G` reads "`H` implies `G`". -/
abbrev ImpRel (Ω : Type*) := Set Ω → Set Ω → Prop

namespace ImpRel

variable (imp : ImpRel Ω)

/-- Axioms `(I1)`–`(I3)`. -/
structure IsDeductive : Prop where
  /-- `(I1)` Transitivity. -/
  trans : ∀ ⦃H G F : Set Ω⦄, imp H G → imp G F → imp H F
  /-- `(I2)` Abstraction. -/
  abstraction : ∀ ⦃H H' G : Set Ω⦄, imp H G → imp H' G → imp (H ∪ H') G
  /-- `(I3)` Monotonicity. -/
  mono : ∀ ⦃H G : Set Ω⦄, H ⊆ G → imp H G

/-- The canonical interpretation of `imp` (eq. `(pi)`): `π(H) = ⋃ {G | G ⇒ H}`. -/
def interp : Interpretation Ω := fun H => ⋃₀ {G | imp G H}

/-- A set of hypotheses `𝓔` is *exact* if no non-empty hypothesis implies two distinct members. -/
def IsExact (𝓔 : Set (Set Ω)) : Prop :=
  ∀ ⦃F⦄, F ∈ 𝓔 → ∀ ⦃G⦄, G ∈ 𝓔 → F ≠ G → ∀ ⦃H : Set Ω⦄, H.Nonempty → imp H F → ¬ imp H G

variable {imp}

theorem subset_interp_of_imp {G H : Set Ω} (h : imp G H) : G ⊆ imp.interp H :=
  subset_sUnion_of_mem h

namespace IsDeductive

variable (hi : imp.IsDeductive)
include hi

theorem refl (H : Set Ω) : imp H H := hi.mono Subset.rfl

/-- Iterated abstraction: a finite union of events each implying `H` implies `H`. -/
theorem sUnion_imp {S : Set (Set Ω)} (hS : S.Finite) {H : Set Ω} (h : ∀ G ∈ S, imp G H) :
    imp (⋃₀ S) H := by
  revert h
  induction S, hS using Set.Finite.induction_on with
  | empty =>
    intro _
    rw [sUnion_empty]
    exact hi.mono (empty_subset H)
  | @insert a s _ _ ih =>
    intro h
    rw [sUnion_insert]
    exact hi.abstraction (h a (mem_insert a s)) (ih fun G hG => h G (mem_insert_of_mem a hG))

variable [Finite Ω]

/-- `π(H) ⇒ H`, where `π` is the canonical interpretation. This is the only place finiteness enters. -/
theorem interp_imp (H : Set Ω) : imp (imp.interp H) H :=
  hi.sUnion_imp (Set.toFinite _) fun _ hG => hG

/-- `G ⇒ H ↔ G ⊆ π(H)`: the canonical interpretation is the upper adjoint of `imp`. -/
theorem imp_iff_subset_interp {G H : Set Ω} : imp G H ↔ G ⊆ imp.interp H :=
  ⟨subset_interp_of_imp, fun h => hi.trans (hi.mono h) (hi.interp_imp H)⟩

/-- **Lemma `lem:drvw`**, sufficiency (coherence). -/
theorem interp_isCoherent : imp.interp.IsCoherent where
  truth H := subset_interp_of_imp (hi.refl H)
  introspection H :=
    Subset.antisymm (hi.imp_iff_subset_interp.1 (hi.trans (hi.interp_imp _) (hi.interp_imp H)))
      (subset_interp_of_imp (hi.refl _))
  mono H _ hHG := hi.imp_iff_subset_interp.1 (hi.trans (hi.interp_imp H) (hi.mono hHG))

/-- **Lemma `lem:drvw`**, sufficiency (interpretation). -/
theorem interp_interprets : imp.interp.Interprets imp := fun H _ =>
  ⟨fun h => hi.imp_iff_subset_interp.1 (hi.trans (hi.interp_imp H) h),
   fun h => hi.imp_iff_subset_interp.2 ((hi.interp_isCoherent.truth H).trans h)⟩

end IsDeductive

end ImpRel

namespace Interpretation.IsCoherent

variable {π : Interpretation Ω} {imp : ImpRel Ω} (hπ : π.IsCoherent) (h : π.Interprets imp)
include hπ h

/-- **Lemma `lem:drvw`**, necessity: an implication relation interpreted by a coherent interpretation
satisfies `(I1)`–`(I3)`. -/
theorem isDeductive : imp.IsDeductive where
  trans := by
    intro H G F h₁ h₂
    exact (h H F).2 (((h H G).1 h₁).trans ((h G F).1 h₂))
  abstraction := by
    intro H H' G h₁ h₂
    refine (h _ G).2 (hπ.subset_iff.2 (union_subset ?_ ?_))
    · exact (hπ.truth H).trans ((h H G).1 h₁)
    · exact (hπ.truth H').trans ((h H' G).1 h₂)
  mono := by
    intro H G hHG
    exact (h H G).2 (hπ.mono hHG)

/-- **Lemma `lem:drvw`**, uniqueness: a coherent interpretation of `imp` is necessarily the canonical
one, `π(H) = ⋃ {G | G ⇒ H}`. No finiteness is required. -/
theorem eq_interp : π = imp.interp := by
  funext H
  ext ω
  rw [ImpRel.interp, mem_sUnion]
  constructor
  · intro hω
    exact ⟨π H, (h (π H) H).2 (hπ.introspection H).subset, hω⟩
  · rintro ⟨G, hG, hωG⟩
    exact (h G H).1 hG (hπ.truth G hωG)

/-- Under a coherent interpretation, a set of hypotheses is exact iff the interpretations of its
members are pairwise disjoint. -/
theorem isExact_iff {𝓔 : Set (Set Ω)} : imp.IsExact 𝓔 ↔ 𝓔.PairwiseDisjoint π := by
  have key : ∀ ω F, imp {ω} F ↔ ω ∈ π F := fun ω F => by
    rw [h {ω} F, hπ.subset_iff, singleton_subset_iff]
  constructor
  · intro hE F hF G hG hFG
    show Disjoint (π F) (π G)
    rw [disjoint_left]
    intro ω hωF hωG
    exact hE hF hG hFG (singleton_nonempty ω) ((key ω F).2 hωF) ((key ω G).2 hωG)
  · rintro hD F hF G hG hFG H ⟨ω, hω⟩ hHF hHG
    have hF' : H ⊆ π F := hπ.subset_iff.1 ((h H F).1 hHF)
    have hG' : H ⊆ π G := hπ.subset_iff.1 ((h H G).1 hHG)
    exact disjoint_left.1 (hD hF hG hFG : Disjoint (π F) (π G)) (hF' hω) (hG' hω)

end Interpretation.IsCoherent

namespace ImpRel

variable {imp : ImpRel Ω}

/-- If some coherent interpretation interprets `imp`, then `imp` satisfies `(I1)`–`(I3)`. -/
theorem isDeductive_of_exists (h : ∃ π : Interpretation Ω, π.IsCoherent ∧ π.Interprets imp) :
    imp.IsDeductive :=
  let ⟨_, hπ, hint⟩ := h
  hπ.isDeductive hint

variable [Finite Ω]

/-- **Lemma `lem:drvw`.** `imp` satisfies `(I1)`–`(I3)` iff the canonical map `(pi)` is a coherent
interpretation of `imp` and every coherent interpretation of `imp` coincides with it. -/
theorem isDeductive_iff : imp.IsDeductive ↔
    imp.interp.IsCoherent ∧ imp.interp.Interprets imp ∧
      ∀ π : Interpretation Ω, π.IsCoherent → π.Interprets imp → π = imp.interp :=
  ⟨fun hi => ⟨hi.interp_isCoherent, hi.interp_interprets, fun _ hπ h => hπ.eq_interp h⟩,
   fun ⟨hc, hint, _⟩ => hc.isDeductive hint⟩

/-- **Lemma `lem:drvw`**, existence-and-uniqueness form. -/
theorem isDeductive_iff_existsUnique :
    imp.IsDeductive ↔ ∃! π : Interpretation Ω, π.IsCoherent ∧ π.Interprets imp :=
  ⟨fun hi => ⟨imp.interp, ⟨hi.interp_isCoherent, hi.interp_interprets⟩,
      fun _ ⟨hπ, h⟩ => hπ.eq_interp h⟩,
   fun ⟨_, ⟨hπ, h⟩, _⟩ => hπ.isDeductive h⟩

theorem isDeductive_iff_exists :
    imp.IsDeductive ↔ ∃ π : Interpretation Ω, π.IsCoherent ∧ π.Interprets imp :=
  ⟨fun hi => ⟨imp.interp, hi.interp_isCoherent, hi.interp_interprets⟩, isDeductive_of_exists⟩

end ImpRel

/-! ## Acts and bets (§3.1) -/

/-- An *act*: a state-contingent payoff, in utils. -/
abbrev Act (Ω : Type*) := Ω → ℝ≥0

/-- The bet `x_H`, paying `x` on `H` and `0` elsewhere. The constant act `x` is `bet x univ`. -/
noncomputable def bet (x : ℝ≥0) (H : Set Ω) : Act Ω := H.indicator fun _ => x

section bet

variable {x : ℝ≥0} {H : Set Ω} {ω : Ω}

@[simp] theorem bet_of_mem (h : ω ∈ H) : bet x H ω = x := by simp [bet, h]

@[simp] theorem bet_of_notMem (h : ω ∉ H) : bet x H ω = 0 := by simp [bet, h]

@[simp] theorem bet_empty (x : ℝ≥0) : bet x (∅ : Set Ω) = 0 := by funext ω; simp [bet]

@[simp] theorem bet_univ (x : ℝ≥0) : bet x (univ : Set Ω) = fun _ => x := by funext ω; simp [bet]

@[simp] theorem bet_zero (H : Set Ω) : bet 0 H = 0 := by funext ω; simp [bet]

end bet

namespace Act

/-- `𝓗(f)`: the hypotheses on which the payoffs of `f` depend, i.e. the non-null level sets of `f`. -/
def hyps (f : Act Ω) : Set (Set Ω) := {H | ∃ ω, 0 < f ω ∧ H = f ⁻¹' {f ω}}

/-- `𝓗(𝓐') = ⋃_{f ∈ 𝓐'} 𝓗(f)`. -/
def hypsOf (A : Set (Act Ω)) : Set (Set Ω) := ⋃ f ∈ A, hyps f

end Act

/-! ## Preferences and revealed implication (§3.1–3.2) -/

/-- A preference relation over acts: reflexive and transitive. -/
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

end Preference

@[inherit_doc] scoped notation:50 f:51 " ≿[" P "] " g:51 => Preference.rel P f g
@[inherit_doc] scoped notation:50 f:51 " ∼[" P "] " g:51 => Preference.Indiff P f g
@[inherit_doc] scoped notation:50 f:51 " ≻[" P "] " g:51 => Preference.Strict P f g

namespace Preference

variable {P : Preference Ω} {f g h : Act Ω}

theorem Indiff.rfl : f ∼[P] f := ⟨P.refl f, P.refl f⟩

theorem Indiff.symm (h₁ : f ∼[P] g) : g ∼[P] f := ⟨h₁.2, h₁.1⟩

theorem Indiff.trans (h₁ : f ∼[P] g) (h₂ : g ∼[P] h) : f ∼[P] h :=
  ⟨P.trans h₁.1 h₂.1, P.trans h₂.2 h₁.2⟩

theorem Indiff.of_eq (e : f = g) : f ∼[P] g := by subst e; exact Indiff.rfl

theorem indiff_equivalence (P : Preference Ω) : Equivalence P.Indiff :=
  ⟨fun _ => Indiff.rfl, Indiff.symm, Indiff.trans⟩

instance (P : Preference Ω) : @Trans (Act Ω) (Act Ω) (Act Ω) P.Indiff P.Indiff P.Indiff :=
  ⟨Indiff.trans⟩

variable (P)

/-- **Revealed implication** (eq. `(imp)`): `H` is revealed to imply `G` iff `1_G ∼ 1_{H ∪ G}`. -/
def revImp : ImpRel Ω := fun H G => bet 1 G ∼[P] bet 1 (H ∪ G)

/-- `π` *interprets* `≿` if it interprets the revealed implication of `≿` (eq. `(int)`). -/
def IsInterpretedBy (π : Interpretation Ω) : Prop := π.Interprets P.revImp

/-- `𝓔` is `≿`-exact. -/
def IsExactSet (𝓔 : Set (Set Ω)) : Prop := P.revImp.IsExact 𝓔

/-- `𝓐^{ex}`: the exact acts, those the DM perceives as unambiguous. -/
def exactActs : Set (Act Ω) := {f | P.IsExactSet (Act.hyps f)}

/-- A collection of acts is exact if `𝓗(𝓐')` is exact. -/
def IsExactCollection (A : Set (Act Ω)) : Prop := P.IsExactSet (Act.hypsOf A)

/-- **Axiom (A1) Modularity**: if `1_G ∼ 1_{G ∪ F}` then `1_{G ∪ H} ∼ 1_{G ∪ H ∪ F}`. -/
def Modularity : Prop :=
  ∀ G F H : Set Ω, bet 1 G ∼[P] bet 1 (G ∪ F) → bet 1 (G ∪ H) ∼[P] bet 1 (G ∪ H ∪ F)

end Preference

@[inherit_doc] scoped notation:50 H:51 " ⇒[" P "] " G:51 => Preference.revImp P H G

namespace Preference

variable (P : Preference Ω)

theorem revImp_iff {H G : Set Ω} : H ⇒[P] G ↔ bet 1 G ∼[P] bet 1 (H ∪ G) := Iff.rfl

/-- Objective implication is revealed: `H ⊆ G → H ⇒ G`. This is `(I3)` for `revImp`, and needs only
reflexivity of `≿`. -/
theorem revImp_of_subset {H G : Set Ω} (h : H ⊆ G) : H ⇒[P] G :=
  Indiff.of_eq (congrArg (bet 1) (union_eq_self_of_subset_left h).symm)

/-- `(A1)` restated in terms of revealed implication: `F ⇒ G` implies `F ⇒ G ∪ H`. -/
theorem modularity_iff :
    P.Modularity ↔ ∀ F G H : Set Ω, F ⇒[P] G → F ⇒[P] (G ∪ H) := by
  constructor
  · intro hmod F G H h
    rw [revImp_iff, union_comm F G] at h
    have h' := hmod G F H h
    rwa [union_comm (G ∪ H) F] at h'
  · intro h G F H hGF
    have h' := h F G H (by rwa [revImp_iff, union_comm F G])
    rwa [revImp_iff, union_comm F (G ∪ H)] at h'

variable {P}

theorem Modularity.revImp_union (hmod : P.Modularity) {F G : Set Ω} (H : Set Ω)
    (h : F ⇒[P] G) : F ⇒[P] (G ∪ H) :=
  P.modularity_iff.1 hmod F G H h

/-- Proof of Theorem 1, first half: `(A1)` implies `(I1)`–`(I3)` for the revealed implication. -/
theorem Modularity.isDeductive (hmod : P.Modularity) : P.revImp.IsDeductive where
  trans := by
    intro H G F hHG hGF
    have h₁ : H ⇒[P] (G ∪ F) := hmod.revImp_union F hHG
    have h₂ : G ⇒[P] (F ∪ H) := hmod.revImp_union H hGF
    show bet 1 F ∼[P] bet 1 (H ∪ F)
    calc bet 1 F ∼[P] bet 1 (G ∪ F) := hGF
      _ ∼[P] bet 1 (H ∪ (G ∪ F)) := h₁
      _ = bet 1 (G ∪ (F ∪ H)) := by
        congr 1; ext; simp only [mem_union]; tauto
      _ ∼[P] bet 1 (F ∪ H) := h₂.symm
      _ = bet 1 (H ∪ F) := by rw [union_comm F H]
  abstraction := by
    intro H H' G hH hH'
    have h₁ : H' ⇒[P] (G ∪ H) := hmod.revImp_union H hH'
    show bet 1 G ∼[P] bet 1 (H ∪ H' ∪ G)
    calc bet 1 G ∼[P] bet 1 (H ∪ G) := hH
      _ = bet 1 (G ∪ H) := by rw [union_comm H G]
      _ ∼[P] bet 1 (H' ∪ (G ∪ H)) := h₁
      _ = bet 1 (H ∪ H' ∪ G) := by
        congr 1; ext; simp only [mem_union]; tauto
  mono := by
    intro H G h
    exact P.revImp_of_subset h

/-- Proof of Theorem 1, second half: `(I1)` and `(I3)` imply `(A1)`. -/
theorem modularity_of_isDeductive (hd : P.revImp.IsDeductive) : P.Modularity :=
  P.modularity_iff.2 fun _ _ _ h => hd.trans h (hd.mono subset_union_left)

/-- `(A1)` is equivalent to `(I1)`–`(I3)` for the revealed implication. No finiteness is needed. -/
theorem modularity_iff_isDeductive : P.Modularity ↔ P.revImp.IsDeductive :=
  ⟨Modularity.isDeductive, modularity_of_isDeductive⟩

/-! ## Theorem 1 -/

/-- **Theorem 1** (`thm:dom`). A preference satisfies `(A1)` if and only if its revealed implication
is interpreted by a coherent interpretation; that interpretation is then unique. -/
theorem modularity_iff_existsUnique [Finite Ω] :
    P.Modularity ↔ ∃! π : Interpretation Ω, π.IsCoherent ∧ P.IsInterpretedBy π :=
  modularity_iff_isDeductive.trans ImpRel.isDeductive_iff_existsUnique

/-- **Theorem 1**, existence form (uniqueness being automatic, by `IsCoherent.eq_interp`). -/
theorem modularity_iff_exists [Finite Ω] :
    P.Modularity ↔ ∃ π : Interpretation Ω, π.IsCoherent ∧ P.IsInterpretedBy π :=
  modularity_iff_isDeductive.trans ImpRel.isDeductive_iff_exists

/-- Under `(A1)`, the canonical interpretation of revealed implication is coherent and interprets `≿`.
-/
theorem Modularity.interp_isCoherent [Finite Ω] (hmod : P.Modularity) :
    P.revImp.interp.IsCoherent ∧ P.IsInterpretedBy P.revImp.interp :=
  ⟨hmod.isDeductive.interp_isCoherent, hmod.isDeductive.interp_interprets⟩

namespace IsInterpretedBy

variable {π : Interpretation Ω} (hπ : π.IsCoherent) (h : P.IsInterpretedBy π)
include hπ h

/-- **Identification** (text following Theorem 1): `π(G) = ⋃ {H | 1_G ∼ 1_{G ∪ H}}`. -/
theorem eq_sUnion (G : Set Ω) : π G = ⋃₀ {H | bet 1 G ∼[P] bet 1 (G ∪ H)} := by
  rw [Interpretation.IsCoherent.eq_interp hπ h]
  show ⋃₀ {H | H ⇒[P] G} = _
  congr 1
  ext H
  show bet 1 G ∼[P] bet 1 (H ∪ G) ↔ bet 1 G ∼[P] bet 1 (G ∪ H)
  rw [union_comm H G]

/-- **Identification** (text following Theorem 1): `π(G)` is the largest event `E ⊇ G` with
`1_E ∼ 1_G`, i.e. the largest enlargement of the winning condition the DM regards as worthless. -/
theorem isGreatest (G : Set Ω) :
    IsGreatest {E | G ⊆ E ∧ bet 1 E ∼[P] bet 1 G} (π G) := by
  refine ⟨⟨hπ.truth G, ?_⟩, ?_⟩
  · have h' : bet 1 G ∼[P] bet 1 (π G ∪ G) := (h (π G) G).2 (hπ.introspection G).subset
    rw [union_eq_self_of_subset_right (hπ.truth G)] at h'
    exact h'.symm
  · rintro E ⟨hGE, hE⟩
    have hEG : E ⇒[P] G := by
      rw [revImp_iff, union_eq_self_of_subset_right hGE]
      exact hE.symm
    exact (hπ.truth E).trans ((h E G).1 hEG)

/-- Under a coherent interpretation of `≿`, a set of hypotheses is exact iff the interpretations of its
members are pairwise disjoint. -/
theorem isExactSet_iff {𝓔 : Set (Set Ω)} : P.IsExactSet 𝓔 ↔ 𝓔.PairwiseDisjoint π :=
  Interpretation.IsCoherent.isExact_iff hπ h

end IsInterpretedBy

end Preference

end HEU
