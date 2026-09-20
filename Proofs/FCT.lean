/-
  `FCT_Theorem1.lean`

  A Lean 4 / Mathlib formalization of Theorem 1 of

    E. Piermont and P. Zuazo-Garin, "Failures of Contingent Thinking"
    (the theorem labelled `thm:iounoprob` in the paper).

  STATEMENT (paper).  Let ≽ be the DM's preference over bets (a bet b_Φ is
  indexed by a contingency Φ, a nonempty set of statements).  If ≽ is
  reflexive and transitive then there exists an *interpretation* of ≽:
  a state-space W together with a truth assignment t : K → 2^W satisfying
  the three faithfulness conditions (F1)-(F3) of Definition 3.

  ON THE DOMAIN K.  The paper takes `K` to be the *nonempty* subsets of
  the language `L` (Section 2.1). Nonemptiness plays no role anywhere in
  the proof of Theorem 1: it is never used in Definition 1, in the filter
  machinery, or in verifying (F1)-(F3); its only job in the paper is to
  make `K` closed under `∪`, which `Set L` already is. So below,
  contingencies are simply elements of `Set L` (Mathlib's `∪`/`⊆` apply
  directly, with no wrapper type and no bridge lemmas needed), and the
  theorem is proved for all of `Set L`. This is if anything more general
  than the paper's statement: `∅` comes out `IsNullC`-null automatically
  (since `∅ ∪ Ψ' = Ψ'` always), which is the sensible reading ("the
  impossible event implies everything"), and restricting the conclusion
  to nonempty `Φ, Ψ` recovers the paper's literal class `K`.

  PROOF STRATEGY (paper, Section "Representation" + Appendix).  Subjective
  implication Φ ⇒ Ψ (Definition 1) is itself a preorder on contingencies
  once ≽ is (Lemma `weakorder`).  The paper then develops a general theory
  of filters for an arbitrary preorder R on a set X (Appendix,
  "Preliminaries: Taxonomy of Filters"): up-sets, filters, proper filters,
  and *irreducible* filters, and proves (Lemma `sepoints`) that the
  irreducible filters strongly separate points, via Zorn's Lemma. Taking
  R := ⇒ and X := K, the canonical interpretation (W*, t*) is built by
  letting W* be the set of all irreducible ⇒-filters and t*(Φ) the set of
  states containing Φ; Lemma `statesarefilters` (whose relevant direction
  is proved inline below) shows this (W*, t*) satisfies (F1)-(F3).

  This file reconstructs exactly this route:
    Part 1.  Contingencies (K := Set L) and subjective implication ⇒.
    Part 2.  ⇒ is reflexive and transitive (Lemma `weakorder`).
    Part 3.  The general theory of filters over an arbitrary relation R,
             culminating in the Zorn's-Lemma separation lemma (the
             irreducible-filter half of Lemma `sepoints`).
    Part 4.  Interpretations (Definition 3) and the canonical
             interpretation built from irreducible ⇒-filters.
    Part 5.  Theorem 1 (`thm:iounoprob`).

  Throughout, `SubjImp pref Φ Ψ` is read "Φ (subjectively) implies Ψ",
  i.e. the paper's `Φ ⇒ Ψ`.
-/
import Mathlib.Order.Zorn
import Mathlib.Order.Preorder.Chain

open Set

variable {L : Type*}

/- ##################################################################
   ## Part 1.  Contingencies, bets, subjective implication
   ################################################################## -/

/- A **contingency** — an element of the paper's `K` — is simply a
subset of the language `L` of statements (see the remark on `K` above).
Each contingency `Φ` indexes a bet `b_Φ`, so we identify bets with
contingencies and a "preference over bets" is a relation on `Set L`. -/

/-- The symmetric part `∼` of the DM's preference `≽` over bets:
indifference. -/
def Indiff (pref : Set L → Set L → Prop) (Φ Ψ : Set L) : Prop :=
  pref Φ Ψ ∧ pref Ψ Φ

lemma indiff_symm (pref : Set L → Set L → Prop) {Φ Ψ : Set L}
    (h : Indiff pref Φ Ψ) : Indiff pref Ψ Φ := ⟨h.2, h.1⟩

/- `pref` is taken as an *explicit* argument here (and in `indiff_symm`
above), even though it could in principle be inferred from `htrans`'s
type. Leaving it implicit forces Lean to solve a higher-order unification
problem (`?pref Φ Ψ =?= pref Φ Ψ` for the bound `Φ Ψ` inside `htrans`'s
`∀`) to determine `pref`, and at the call site in `subjImp_trans` below —
where this lemma is applied twice, once nested inside the other — that
unification can be deferred and resolved against the wrong metavariable,
producing a spurious type mismatch. Supplying `pref` explicitly sidesteps
the higher-order unification entirely. -/
lemma indiff_trans (pref : Set L → Set L → Prop)
    (htrans : ∀ {Φ Ψ Λ : Set L}, pref Φ Ψ → pref Ψ Λ → pref Φ Λ)
    {Φ Ψ Λ : Set L} (h1 : Indiff pref Φ Ψ) (h2 : Indiff pref Ψ Λ) :
    Indiff pref Φ Λ :=
  ⟨htrans h1.1 h2.1, htrans h2.2 h1.2⟩

/-- **Definition 1 (Subjective implication).**  `Φ` is perceived to imply
`Ψ` — the paper's `Φ ⇒ Ψ` — if for every `Ψ' ⊇ Ψ` the DM is indifferent
between betting on `Ψ'` and on `Φ ∪ Ψ'`. -/
def SubjImp (pref : Set L → Set L → Prop) (Φ Ψ : Set L) : Prop :=
  ∀ Ψ' : Set L, Ψ ⊆ Ψ' → Indiff pref Ψ' (Φ ∪ Ψ')

/-- A contingency is **null** if it is perceived to imply everything
(paper, Definition 2). -/
def IsNullC (pref : Set L → Set L → Prop) (Φ : Set L) : Prop :=
  ∀ Ψ, SubjImp pref Φ Ψ

/- ##################################################################
   ## Part 2.  ⇒ is reflexive and transitive  (paper's Lemma `weakorder`)
   ################################################################## -/

lemma subjImp_refl (pref : Set L → Set L → Prop)
    (hrefl : ∀ Φ, pref Φ Φ) (Φ : Set L) : SubjImp pref Φ Φ := by
  intro Ψ' hsub
  have heq : Φ ∪ Ψ' = Ψ' := Set.union_eq_self_of_subset_left hsub
  rw [heq]
  exact ⟨hrefl Ψ', hrefl Ψ'⟩

/-- **Lemma `weakorder`** (transitivity half; reflexivity is
`subjImp_refl`).  This is the paper's computation
`b_{Λ'} ∼ b_{Ψ∪Λ'} ∼ b_{Φ∪(Ψ∪Λ')} = b_{Ψ∪(Φ∪Λ')} ∼ b_{Φ∪Λ'}`. -/
lemma subjImp_trans (pref : Set L → Set L → Prop)
    (htrans : ∀ {Φ Ψ Λ : Set L}, pref Φ Ψ → pref Ψ Λ → pref Φ Λ) :
    ∀ {Φ Ψ Λ : Set L}, SubjImp pref Φ Ψ → SubjImp pref Ψ Λ → SubjImp pref Φ Λ := by
  intro Φ Ψ Λ hΦΨ hΨΛ Λ' hΛΛ'
  -- b_{Λ'} ∼ b_{Ψ∪Λ'}
  have step1 : Indiff pref Λ' (Ψ ∪ Λ') := hΨΛ Λ' hΛΛ'
  -- b_{Ψ∪Λ'} ∼ b_{Φ∪(Ψ∪Λ')}
  have step2 : Indiff pref (Ψ ∪ Λ') (Φ ∪ (Ψ ∪ Λ')) :=
    hΦΨ (Ψ ∪ Λ') Set.subset_union_left
  -- Φ∪(Ψ∪Λ') = Ψ∪(Φ∪Λ') as sets
  have hEq : Φ ∪ (Ψ ∪ Λ') = Ψ ∪ (Φ ∪ Λ') := by
    rw [← Set.union_assoc, Set.union_comm Φ Ψ, Set.union_assoc]
  have step2' : Indiff pref (Ψ ∪ Λ') (Ψ ∪ (Φ ∪ Λ')) := by rw [← hEq]; exact step2
  -- b_{Φ∪Λ'} ∼ b_{Ψ∪(Φ∪Λ')}
  have hΛsub : Λ ⊆ Φ ∪ Λ' := Set.Subset.trans hΛΛ' Set.subset_union_right
  have step4 : Indiff pref (Φ ∪ Λ') (Ψ ∪ (Φ ∪ Λ')) := hΨΛ (Φ ∪ Λ') hΛsub
  -- chain them together
  exact indiff_trans pref htrans (indiff_trans pref htrans step1 step2') (indiff_symm pref step4)

/- ##################################################################
   ## Part 3.  General filter theory over an arbitrary relation
   ## (paper's Appendix, "Preliminaries: Taxonomy of Filters")
   ################################################################## -/

namespace FilterTheory

variable {X : Type*}

/-- `x` is **null** for `R` if `x R y` for every `y`. -/
def IsNull (R : X → X → Prop) (x : X) : Prop := ∀ y, R x y

/-- `Y` is an `R`-**up-set**. -/
def IsUpSet (R : X → X → Prop) (Y : Set X) : Prop :=
  ∀ ⦃x y⦄, x ∈ Y → R x y → y ∈ Y

/-- A **filter**: a nonempty up-set that is downward directed. -/
structure IsFilter (R : X → X → Prop) (Y : Set X) : Prop where
  nonempty : Y.Nonempty
  upSet : IsUpSet R Y
  directed : ∀ ⦃x y⦄, x ∈ Y → y ∈ Y → ∃ z ∈ Y, R z x ∧ R z y

/-- A filter is **proper** if it contains no null element. -/
structure IsProperFilter (R : X → X → Prop) (Y : Set X) : Prop where
  filter : IsFilter R Y
  proper : ∀ x ∈ Y, ¬ IsNull R x

/-- A proper filter `f` is **irreducible** if, whenever it arises as the
intersection of a nonempty family of proper filters, it is one of them
(paper, equation `eq:irr`). -/
def IsIrreducible (R : X → X → Prop) (f : Set X) : Prop :=
  IsProperFilter R f ∧
    ∀ 𝔊 : Set (Set X), 𝔊.Nonempty → (∀ g ∈ 𝔊, IsProperFilter R g) →
      (⋂ g ∈ 𝔊, g) = f → f ∈ 𝔊

/-- A family `𝔍` of filters **strongly separates points** if every
proper filter `f` can be extended to some member of `𝔍` while continuing
to avoid any chosen point outside `f`. -/
def StronglySeparatesPoints (R : X → X → Prop) (𝔍 : Set (Set X)) : Prop :=
  ∀ f, IsProperFilter R f → ∀ x, x ∉ f → ∃ g ∈ 𝔍, f ⊆ g ∧ x ∉ g

/-- The union of a nonempty `⊆`-chain of proper filters is again a proper
filter.  This is the "standard arguments" step of the paper's proof of
Lemma `sepoints`, spelled out. -/
private lemma properFilter_sUnion_chain (R : X → X → Prop) {c : Set (Set X)}
    (hcnonempty : c.Nonempty) (hcF : ∀ Y ∈ c, IsProperFilter R Y)
    (hchain : IsChain (· ⊆ ·) c) : IsProperFilter R (⋃₀ c) where
  filter :=
  { nonempty := by
      obtain ⟨Y, hY⟩ := hcnonempty
      obtain ⟨y, hy⟩ := (hcF Y hY).filter.nonempty
      exact ⟨y, Y, hY, hy⟩
    upSet := by
      rintro x y ⟨Y, hY, hxY⟩ hxy
      exact ⟨Y, hY, (hcF Y hY).filter.upSet hxY hxy⟩
    directed := by
      rintro x y ⟨Y1, hY1, hxY1⟩ ⟨Y2, hY2, hyY2⟩
      rcases hchain.total hY1 hY2 with hsub | hsub
      · obtain ⟨z, hz, hzx, hzy⟩ := (hcF Y2 hY2).filter.directed (hsub hxY1) hyY2
        exact ⟨z, ⟨Y2, hY2, hz⟩, hzx, hzy⟩
      · obtain ⟨z, hz, hzx, hzy⟩ := (hcF Y1 hY1).filter.directed hxY1 (hsub hyY2)
        exact ⟨z, ⟨Y1, hY1, hz⟩, hzx, hzy⟩ }
  proper := by
    rintro x ⟨Y, hY, hxY⟩
    exact (hcF Y hY).proper x hxY

/-- **Lemma `sepoints`, irreducible-filter half.**  For any relation `R`
on `X`, the irreducible `R`-filters strongly separate points.

Proof (paper, Appendix).  Fix a proper filter `f` and a point `x ∉ f`.
Among proper filters extending `f` and avoiding `x`, take a maximal one
`𝔦` (Zorn's Lemma; the union of a chain of such filters is again such a
filter, by `properFilter_sUnion_chain`). If `𝔦` were the intersection of
a family `𝔊` of proper filters none equal to `𝔦`, then `𝔦 ⊆ g` for every
`g ∈ 𝔊`; since `g ≠ 𝔦`, each such `g` strictly contains `𝔦` while still
containing `f`, so by maximality of `𝔦` each `g` must contain `x`
(otherwise `g` itself would lie in the competing family, contradicting
maximality of `𝔦`). Hence `x ∈ ⋂ 𝔊`, contradicting `x ∉ 𝔦 = ⋂ 𝔊`. So `𝔦`
is irreducible. -/
theorem irreducible_stronglySeparatesPoints (R : X → X → Prop) :
    StronglySeparatesPoints R {g : Set X | IsIrreducible R g} := by
  intro f hf x hx
  let F : Set (Set X) := {Y | IsProperFilter R Y ∧ f ⊆ Y ∧ x ∉ Y}
  have hfF : f ∈ F := ⟨hf, Set.Subset.refl f, hx⟩
  have hzorn : ∀ c ⊆ F, IsChain (· ⊆ ·) c → ∃ ub ∈ F, ∀ Y ∈ c, Y ⊆ ub := by
    intro c hcF hchain
    rcases c.eq_empty_or_nonempty with rfl | hcne
    · exact ⟨f, hfF, by simp⟩
    · have hcF' : ∀ Y ∈ c, IsProperFilter R Y := fun Y hY => (hcF hY).1
      refine ⟨⋃₀ c, ⟨properFilter_sUnion_chain R hcne hcF' hchain, ?_, ?_⟩,
        fun Y hY => Set.subset_sUnion_of_mem hY⟩
      · obtain ⟨Y0, hY0⟩ := hcne
        exact Set.Subset.trans (hcF hY0).2.1 (Set.subset_sUnion_of_mem hY0)
      · rintro ⟨Y, hY, hxY⟩
        exact (hcF hY).2.2 hxY
  obtain ⟨𝔦, h𝔦max⟩ := zorn_subset F hzorn
  have h𝔦F : 𝔦 ∈ F := h𝔦max.1
  refine ⟨𝔦, ?_, h𝔦F.2.1, h𝔦F.2.2⟩
  refine ⟨h𝔦F.1, ?_⟩
  rintro 𝔊 h𝔊ne h𝔊proper h𝔊inter
  by_contra h𝔦notin
  have hsub : ∀ g ∈ 𝔊, 𝔦 ⊆ g := by
    intro g hg
    rw [← h𝔊inter]
    exact Set.iInter₂_subset g hg
  have hxmem : ∀ g ∈ 𝔊, x ∈ g := by
    intro g hg
    by_contra hxg
    have hgF : g ∈ F := ⟨h𝔊proper g hg, Set.Subset.trans h𝔦F.2.1 (hsub g hg), hxg⟩
    have hg𝔦sub : g ⊆ 𝔦 := h𝔦max.2 hgF (hsub g hg)
    have hgeq : g = 𝔦 := Set.Subset.antisymm hg𝔦sub (hsub g hg)
    rw [hgeq] at hg
    exact h𝔦notin hg
  have hxinter : x ∈ ⋂ g ∈ 𝔊, g := Set.mem_iInter₂_of_mem hxmem
  rw [h𝔊inter] at hxinter
  exact h𝔦F.2.2 hxinter

end FilterTheory

/- ##################################################################
   ## Part 4.  Interpretations, and the canonical interpretation
   ################################################################## -/

/-- The principal `⇒`-filter generated by `Φ`: those `Ψ` that `Φ` is
perceived to imply. -/
def principalFilter (pref : Set L → Set L → Prop) (Φ : Set L) : Set (Set L) :=
  {Ψ | SubjImp pref Φ Ψ}

lemma principalFilter_isFilter (pref : Set L → Set L → Prop)
    (hrefl : ∀ Φ, pref Φ Φ)
    (htrans : ∀ {Φ Ψ Λ : Set L}, pref Φ Ψ → pref Ψ Λ → pref Φ Λ)
    (Φ : Set L) :
    FilterTheory.IsFilter (SubjImp pref) (principalFilter pref Φ) where
  nonempty := ⟨Φ, subjImp_refl pref hrefl Φ⟩
  upSet := by
    intro Ψ Λ hΨ hΨΛ
    exact subjImp_trans pref htrans hΨ hΨΛ
  directed := by
    intro Ψ Λ hΨ hΛ
    exact ⟨Φ, subjImp_refl pref hrefl Φ, hΨ, hΛ⟩

lemma principalFilter_isProperFilter (pref : Set L → Set L → Prop)
    (hrefl : ∀ Φ, pref Φ Φ)
    (htrans : ∀ {Φ Ψ Λ : Set L}, pref Φ Ψ → pref Ψ Λ → pref Φ Λ)
    {Φ : Set L} (hΦnn : ¬ IsNullC pref Φ) :
    FilterTheory.IsProperFilter (SubjImp pref) (principalFilter pref Φ) where
  filter := principalFilter_isFilter pref hrefl htrans Φ
  proper := by
    intro Ψ hΨ hΨnull
    exact hΦnn (fun Γ => subjImp_trans pref htrans hΨ (hΨnull Γ))

/-- **Definition 3 (Interpretation).**  A pair `(W, t)` — `W` a
state-space (a set of subsets of `K`, i.e. `W ⊆ 2^K \ ∅` in the paper's
notation) and `t` the induced truth assignment `t Φ = {w ∈ W | Φ ∈ w}` —
is an **interpretation** of `pref` if it satisfies the paper's three
faithfulness conditions (F1)-(F3). -/
structure IsInterpretation (pref : Set L → Set L → Prop)
    (W : Set (Set (Set L))) (t : Set L → Set (Set (Set L))) : Prop where
  ht : ∀ Φ, t Φ = {w ∈ W | Φ ∈ w}
  F1 : ∀ Φ Ψ, t Φ ⊆ t Ψ ↔ SubjImp pref Φ Ψ
  F2 : ∀ Φ, t Φ = ∅ ↔ IsNullC pref Φ
  F3 : ∀ Φ Ψ w, w ∈ t Φ ∩ t Ψ → ∃ Γ, w ∈ t Γ ∧ SubjImp pref Γ Φ ∧ SubjImp pref Γ Ψ

/- ##################################################################
   ## Part 5.  Theorem 1  (`thm:iounoprob`)
   ################################################################## -/

/-- **Theorem 1** (paper, `thm:iounoprob`).  If `pref` — the DM's
preference `≽` over bets — is reflexive and transitive, then there exists
an interpretation of `pref`.

Proof.  Let `W` be the set of irreducible `⇒`-filters and
`t Φ := {w ∈ W | Φ ∈ w}` (the canonical interpretation `(W*, t*)` of the
paper's Definition, "Canonical interpretation").  We check (F1)-(F3):

* (F1, ⇐) If `Φ ⇒ Ψ` and `w ∈ t Φ`, then `Φ ∈ w` and, since `w` is an
  `⇒`-up-set (part of being a filter), `Ψ ∈ w`, so `w ∈ t Ψ`.
* (F1, ⇒) Suppose `¬ (Φ ⇒ Ψ)`. Then `Φ` is not null (else it would imply
  everything, including `Ψ`), so the principal filter `f_Φ` is proper; it
  contains `Φ` (reflexivity) but not `Ψ`. By the separation lemma there is
  an irreducible filter `w ⊇ f_Φ` with `Ψ ∉ w`; then `Φ ∈ w`, so
  `w ∈ t Φ \ t Ψ`, whence `t Φ ⊄ t Ψ`.
* (F2, ⇐) If `Φ` is null then every proper filter excludes it (properness),
  so `t Φ = ∅`.
* (F2, ⇒) If `Φ` is not null, pick `Ψ₀` with `¬(Φ ⇒ Ψ₀)`; as in (F1, ⇒),
  separating `f_Φ` from `Ψ₀` produces an irreducible filter containing
  `Φ`, so `t Φ ≠ ∅`.
* (F3) If `w ∈ t Φ ∩ t Ψ` then `Φ, Ψ ∈ w`; since `w` is a filter, some
  `Γ ∈ w` satisfies `Γ ⇒ Φ` and `Γ ⇒ Ψ`, and `w ∈ t Γ`. -/
theorem exists_interpretation (pref : Set L → Set L → Prop)
    (hrefl : ∀ Φ, pref Φ Φ)
    (htrans : ∀ {Φ Ψ Λ : Set L}, pref Φ Ψ → pref Ψ Λ → pref Φ Λ) :
    ∃ (W : Set (Set (Set L))) (t : Set L → Set (Set (Set L))),
      IsInterpretation pref W t := by
  classical
  let W : Set (Set (Set L)) := {w | FilterTheory.IsIrreducible (SubjImp pref) w}
  let t : Set L → Set (Set (Set L)) := fun Φ => {w ∈ W | Φ ∈ w}
  refine ⟨W, t, ⟨fun _ => rfl, ?_, ?_, ?_⟩⟩
  · -- (F1)
    intro Φ Ψ
    constructor
    · intro hsub
      by_contra hnotimp
      have hΦnn : ¬ IsNullC pref Φ := fun hnull => hnotimp (hnull Ψ)
      have hΦmemPF : Φ ∈ principalFilter pref Φ := subjImp_refl pref hrefl Φ
      have hΨnotmemPF : Ψ ∉ principalFilter pref Φ := hnotimp
      have hPFproper := principalFilter_isProperFilter pref hrefl htrans hΦnn
      obtain ⟨w, hwmem, hPFsub, hΨnotw⟩ :=
        FilterTheory.irreducible_stronglySeparatesPoints (SubjImp pref)
          (principalFilter pref Φ) hPFproper Ψ hΨnotmemPF
      have hΦw : Φ ∈ w := hPFsub hΦmemPF
      have hwt : w ∈ t Φ := ⟨hwmem, hΦw⟩
      exact hΨnotw (hsub hwt).2
    · intro hΦΨ w hw
      exact ⟨hw.1, hw.1.1.filter.upSet hw.2 hΦΨ⟩
  · -- (F2)
    intro Φ
    constructor
    · -- t Φ = ∅ → Φ is null
      intro htempty
      by_contra hΦnotnull
      have hΦmemPF : Φ ∈ principalFilter pref Φ := subjImp_refl pref hrefl Φ
      have hPFproper := principalFilter_isProperFilter pref hrefl htrans hΦnotnull
      have hex : ∃ Ψ₀, ¬ SubjImp pref Φ Ψ₀ := by
        by_contra hall
        apply hΦnotnull
        intro Ψ₀
        by_contra hΨ₀
        exact hall ⟨Ψ₀, hΨ₀⟩
      obtain ⟨Ψ₀, hΨ₀⟩ := hex
      obtain ⟨w, hwmem, hPFsub, _⟩ :=
        FilterTheory.irreducible_stronglySeparatesPoints (SubjImp pref)
          (principalFilter pref Φ) hPFproper Ψ₀ hΨ₀
      have hΦw : Φ ∈ w := hPFsub hΦmemPF
      have hmem : w ∈ t Φ := ⟨hwmem, hΦw⟩
      rw [htempty] at hmem
      exact (Set.mem_empty_iff_false w).mp hmem
    · -- Φ is null → t Φ = ∅
      intro hnull
      ext w
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hw
      exact hw.1.1.proper Φ hw.2 hnull
  · -- (F3)
    intro Φ Ψ w hw
    obtain ⟨hwΦ, hwΨ⟩ := hw
    obtain ⟨hwW, hΦw⟩ := hwΦ
    obtain ⟨-, hΨw⟩ := hwΨ
    obtain ⟨Γ, hΓw, hΓΦ, hΓΨ⟩ := hwW.1.filter.directed hΦw hΨw
    exact ⟨Γ, ⟨hwW, hΓw⟩, hΓΦ, hΓΨ⟩
