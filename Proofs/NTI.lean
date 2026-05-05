import Mathlib.Data.Set.Lattice
set_option linter.style.whitespace false

-- ==========================================
-- Prelim: Definitions
-- ==========================================


variable {A : Type}

-- R represents the stringent implication relation (⇒)
variable (R : A → A → Prop)

-- w_a and m_a
def up_set (a : A) : Set A := { b | R a b }
def down_set (a : A) : Set A := { b | R b a}


/-- A tight representation of R on a state space W: maps 'ver' (verification)
    and 'fc' (complement of falsification) satisfying (R), (T1), and (T2). -/
structure TightRep (R : A → A → Prop) where
  W         : Type
  ver       : A → Set W
  fc        : A → Set W
  rep       : ∀ a b, R a b ↔ fc a ⊆ ver b
  tight_ver : ∀ a, ver a = ⋃ b ∈ {x | R x a}, fc b
  tight_fc  : ∀ a, fc a = ⋂ b ∈ {x | R a x}, ver b

/-- A plain (possibly non-tight) representation of R. -/
structure Rep (R : A → A → Prop) where
  W   : Type
  ver : A → Set W
  fc  : A → Set W
  rep : ∀ a b, R a b ↔ fc a ⊆ ver b


-- def IsLeniency (R imp : A → A → Prop) : Prop :=
--   ∀ a b, imp a b ↔ ∀ c, R c a → up_set R b ⊆ up_set R c

def leniency (R : A → A → Prop) (a b : A) : Prop :=
  ∀ c, R c a → up_set R b ⊆ up_set R c

  /-- A plausibility representation witnessing n is plausible for R:
    a joint state space with ver/fc representing R and tn representing n,
    satisfying ver(a) ⊆ tn(a) ⊆ fc(a) for all a. -/
structure PlausRep (R n : A → A → Prop) where
  W   : Type
  ver : A → Set W
  fc  : A → Set W
  tn  : A → Set W
  rep : ∀ a b, R a b ↔ fc a ⊆ ver b       -- (R):  R iff fc(a) ⊆ ver(b)
  sub : ∀ a b, n a b ↔ tn a ⊆ tn b         -- (P1): n iff tn(a) ⊆ tn(b)
  con : ∀ a, ver a ⊆ tn a ∧ tn a ⊆ fc a   -- (P2): ver(a) ⊆ tn(a) ⊆ fc(a)

/-- n is plausible for R: R ⊆ n, n is a preorder, and n ⊆ leniency(R).
    Leniency is expanded inline: n a b implies for all c, R c a → up_set R b ⊆ up_set R c. -/
structure IsPlausible (R n : A → A → Prop) : Prop where
  n_refl  : ∀ a, n a a
  n_trans : ∀ {a b c}, n a b → n b c → n a c
  R_le_n  : ∀ a b, R a b → n a b
  n_le    : ∀ a b, n a b → leniency R a b

-- ==========================================
-- Theorem 1: Existence of a Tight Representation
-- ==========================================

-- define canonical structure: v(a) and f^c(a)
def v (a : A) : Set A := { z | a ∈ up_set R z }
def f_c (a : A) : Set A := { z | up_set R a ⊆ up_set R z }

-- -------------------------------------------------------
-- Part 1: The Representation Property (R)
-- a ⇒ b if and only if f^c(a) ⊆ v(b)
-- -------------------------------------------------------
theorem representation_property (a b : A) :
    R a b ↔ f_c R a ⊆ v R b := by
  constructor
  · intro hab z hz
    exact hz hab
  · intro h
    have ha : a ∈ f_c R a := fun x hx => hx
    exact h ha

-- -------------------------------------------------------
-- Part 2: Tightness Property (T1)
-- v(a) = ⋃_{b ∈ m_a} f^c(b)
-- -------------------------------------------------------
theorem tightness_T1 (a : A) :
    v R a = ⋃ b ∈ { x | R x a }, f_c R b := by
  ext z
  constructor
  · intro hz
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨z, hz, fun x hx => hx⟩
  · intro hz
    simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hz
    obtain ⟨b, hba, hzfcb⟩ := hz
    exact hzfcb hba

-- -------------------------------------------------------
-- Part 3: Tightness Property (T2)
-- f^c(a) = ⋂_{b ∈ w_a} v(b)
-- -------------------------------------------------------
theorem tightness_T2 (a : A) :
    f_c R a = ⋂ b ∈ { x | R a x }, v R b := by
  ext z
  simp [f_c, v, up_set]


/-- The canonical tight representation, with state space A itself. -/
def canonTightRep : TightRep R :=
  { W         := A
    ver       := v R
    fc        := f_c R
    rep       := representation_property R
    tight_ver := tightness_T1 R
    tight_fc  := tightness_T2 R }

/-- Theorem 1: Every relation R admits a tight representation.
    Proved by exhibiting the canonical one. -/
theorem exists_tight_rep : Nonempty (TightRep R) :=
  ⟨canonTightRep R⟩

-- ==========================================
-- Theorem 2: Characterization of Leniency
-- ==========================================

-- -------------------------------------------------------
-- Theorem 2, (1) → (2):
-- imp is a leniency implies
-- imp a b ↔ v(a) ⊆ f_c(b) in every tight rep
-- -------------------------------------------------------

theorem leniency_imp_allTightReps :
    ∀ a b, leniency R a b → ∀ tr : TightRep R, tr.ver a ⊆ tr.fc b := by
  intro a b
  · -- leniency R a b → every tight rep has ver(a) ⊆ fc(b)
    intro hab tr z hz
    simp_rw [tr.tight_ver a, Set.mem_iUnion, Set.mem_setOf_eq] at hz
    rcases hz with ⟨c, hca, hzfc⟩

    -- `hab` is directly the definition of leniency.
    -- We can just apply it to `c` and `hca`.
    have hpush : up_set R b ⊆ up_set R c := hab c hca

    -- Use T2: fc(b) = ⋂_{d ∈ w_b} ver(d)
    simp_rw [tr.tight_fc b, Set.mem_iInter, Set.mem_setOf_eq]
    intro d hbd
    exact (tr.rep c d).mp (hpush hbd) hzfc

-- -------------------------------------------------------
-- Theorem 2, (2) → (3):
-- imp a b ↔ v(a) ⊆ f_c(b) in every tight rep implies
-- imp a b ↔ v(a) ⊆ f_c(b) in some rep
-- -------------------------------------------------------

theorem allTightReps_imp_someRep (imp : A → A → Prop)
    (h2 : ∀ a b, imp a b ↔ ∀ tr : TightRep R, tr.ver a ⊆ tr.fc b) :
    ∀ a b, imp a b → ∃ r : Rep R, r.ver a ⊆ r.fc b := by
  intro a b hab
  exact ⟨{ W := A, ver := v R, fc := f_c R, rep := representation_property R },
         (h2 a b).mp hab (canonTightRep R)⟩

-- -------------------------------------------------------
-- Theorem 2, (3) → (1):
-- imp a b ↔ v(a) ⊆ f_c(b) in some rep implies
-- imp is a leniency
-- -------------------------------------------------------

theorem someRep_imp_leniency :
 ∀ a b, (∃ r : Rep R, r.ver a ⊆ r.fc b) → leniency R a b := by
  intro a b
  · intro hExists
    obtain ⟨r, hrep⟩ := hExists
    intro c hca d hbd
    exact (r.rep c d).mpr <| ((r.rep c a).mp hca).trans <| hrep.trans ((r.rep b d).mp hbd)

-- ==========================================
-- Theorem 3: Plausibility Characterization
-- ==========================================

/-- Membership in down_set unfolds to the relation. -/
private lemma mem_down_set {n : A → A → Prop} {a c : A} :
    c ∈ down_set n a ↔ n c a :=
  Iff.rfl

-- -------------------------------------------------------
-- Theorem 3, Direction (sandwich → plausible):
-- A plausibility representation implies IsPlausible.
-- -------------------------------------------------------

/-- Given a PlausRep, extract plausibility.
    The proof of n_le relies on a direct subset chain through the representation:
    fc(c) ⊆ ver(a) ⊆ tn(a) ⊆ tn(b) ⊆ fc(b) ⊆ ver(d) implies R c d. -/
theorem plausRep_implies_plausible (n : A → A → Prop) (pr : PlausRep R n) :
    IsPlausible R n where

  n_refl a := by
    -- Reflexivity: tn a ⊆ tn a
    apply (pr.sub a a).mpr
    exact subset_rfl

  n_trans {a b c} hab hbc := by
    -- Transitivity: chain tn a ⊆ tn b ⊆ tn c
    apply (pr.sub a c).mpr
    calc pr.tn a
      _ ⊆ pr.tn b := (pr.sub a b).mp hab
      _ ⊆ pr.tn c := (pr.sub b c).mp hbc

  R_le_n a b hab := by
    -- R ⊆ n: chain tn a ⊆ fc a ⊆ ver b ⊆ tn b
    apply (pr.sub a b).mpr
    calc pr.tn a
      _ ⊆ pr.fc a  := (pr.con a).2
      _ ⊆ pr.ver b := (pr.rep a b).mp hab
      _ ⊆ pr.tn b  := (pr.con b).1

  n_le a b hab c hca d hbd := by
    -- Leniency push: R c a and n a b and R b d implies R c d.
    -- We show R c d by demonstrating fc c ⊆ ver d.
    apply (pr.rep c d).mpr
    calc pr.fc c
      _ ⊆ pr.ver a := (pr.rep c a).mp hca
      _ ⊆ pr.tn a  := (pr.con a).1
      _ ⊆ pr.tn b  := (pr.sub a b).mp hab
      _ ⊆ pr.fc b  := (pr.con b).2
      _ ⊆ pr.ver d := (pr.rep b d).mp hbd

-- -------------------------------------------------------
-- Theorem 3, Direction (plausible → sandwich):
-- The Canonical Plausibility Representation
-- -------------------------------------------------------

/-- The canonical plausibility representation on state space A ⊕ A. -/
def plausCanonRep (n : A → A → Prop) (hp : IsPlausible R n) : PlausRep R n where
  W   := A ⊕ A

  -- State assignments using disjoint unions (Sum.inl for R-states, Sum.inr for n-states)
  ver a := Sum.inl '' v R a    ∪ Sum.inr '' down_set n a
  fc  a := Sum.inl '' f_c R a  ∪ Sum.inr '' down_set n a
  tn  a := Sum.inl '' (⋃ c ∈ down_set n a, v R c) ∪ Sum.inr '' down_set n a

  rep := fun a b => by
    constructor
    · -- Forward: R a b → fc a ⊆ ver b
      intro hab w hw
      -- Unpack the set theory into pure logic
      simp only [Set.mem_union, Set.mem_image, mem_down_set] at hw ⊢
      rcases hw with ⟨w', hw'fc, rfl⟩ | ⟨c, hca, rfl⟩
      · -- Case 1 (Left): w' ∈ f_c R a. By standard R-representation, w' ∈ v R b.
        apply Or.inl
        exact ⟨w', (representation_property R a b).mp hab hw'fc, rfl⟩
      · -- Case 2 (Right): c ∈ m_a^n (i.e., n c a). Transitivity gives n c b.
        apply Or.inr
        exact ⟨c, hp.n_trans hca (hp.R_le_n a b hab), rfl⟩
    · -- Backward: fc a ⊆ ver b → R a b
      intro hfc
      -- 'a' is trivially in f_c R a, so Sum.inl a is in our constructed fc a
      have hainfc : Sum.inl a ∈ Sum.inl '' f_c R a ∪ Sum.inr '' down_set n a := by
        simp only [Set.mem_union, Set.mem_image, mem_down_set]
        exact Or.inl ⟨a, fun _ h => h, rfl⟩
      -- Push it into ver b and unpack
      have hainver := hfc hainfc
      simp only [Set.mem_union, Set.mem_image, mem_down_set] at hainver
      rcases hainver with ⟨w', hw'b, hinl⟩ | ⟨_, _, hinr⟩
      · -- Left Match: Sum.inl w' = Sum.inl a implies w' = a.
        -- Substituting w' = a into hw'b : w' ∈ v R b gives a ∈ v R b (i.e. R a b).
        exact (Sum.inl.inj hinl) ▸ hw'b
      · -- Right Match: impossible
        contradiction

  sub := fun a b => by
    constructor
    · -- Forward: n a b → tn a ⊆ tn b
      intro hab w hw
      simp only [Set.mem_union, Set.mem_image, Set.mem_iUnion, mem_down_set] at hw ⊢
      rcases hw with ⟨w', ⟨c, hca, hw'vc⟩, rfl⟩ | ⟨c, hca, rfl⟩
      · -- Case 1 (Left): n c a and w' ∈ v R c. Transitivity gives n c b.
        apply Or.inl
        exact ⟨w', ⟨c, hp.n_trans hca hab, hw'vc⟩, rfl⟩
      · -- Case 2 (Right): n c a. Transitivity gives n c b.
        apply Or.inr
        exact ⟨c, hp.n_trans hca hab, rfl⟩
    · -- Backward: tn a ⊆ tn b → n a b
      intro htn
      -- 'a' is in its own down-set, so Sum.inr a is in tn a
      have haintn : Sum.inr a ∈
          Sum.inl '' (⋃ c ∈ down_set n a, v R c) ∪
          Sum.inr '' down_set n a := by
        simp only [Set.mem_union, Set.mem_image, Set.mem_iUnion, mem_down_set]
        exact Or.inr ⟨a, hp.n_refl a, rfl⟩
      -- Push into tn b and unpack
      have haintnb := htn haintn
      simp only [Set.mem_union, Set.mem_image, Set.mem_iUnion, mem_down_set] at haintnb
      rcases haintnb with ⟨_, _, hinl⟩ | ⟨c, hcb, hinr⟩
      · contradiction
      · -- Sum.inr c = Sum.inr a implies c = a. Thus n c b becomes n a b.
        exact (Sum.inr.inj hinr) ▸ hcb

  con := fun a => by
    constructor
    · -- Part 1: ver a ⊆ tn a
      intro w hw
      simp only [Set.mem_union, Set.mem_image, Set.mem_iUnion, mem_down_set] at hw ⊢
      rcases hw with ⟨w', hw'va, rfl⟩ | ⟨c, hca, rfl⟩
      · -- Case 1 (Left): w' ∈ v R a. Inject into tn a using c = a (n a a).
        apply Or.inl
        exact ⟨w', ⟨a, hp.n_refl a, hw'va⟩, rfl⟩
      · -- Case 2 (Right): n c a. Directly in the right component.
        apply Or.inr
        exact ⟨c, hca, rfl⟩
    · -- Part 2: tn a ⊆ fc a
      intro w hw
      simp only [Set.mem_union, Set.mem_image, Set.mem_iUnion, mem_down_set] at hw ⊢
      rcases hw with ⟨w', ⟨c, hca, hw'vc⟩, rfl⟩ | ⟨c, hca, rfl⟩
      · -- Case 1 (Left): w' ∈ v R c for some c where n c a.
        -- Inline leniency (n_le) pushes w' directly into f_c R a.
        apply Or.inl
        exact ⟨w', hp.n_le c a hca w' hw'vc, rfl⟩
      · -- Case 2 (Right): n c a. Directly in the right component.
        apply Or.inr
        exact ⟨c, hca, rfl⟩


/-- Theorem 3 (Plausibility Characterization):
    n is plausible for R iff it admits a plausibility representation. -/
theorem plausibility_characterization (n : A → A → Prop) :
    IsPlausible R n ↔ Nonempty (PlausRep R n) :=
  ⟨fun hp  => ⟨plausCanonRep R n hp⟩,
   fun ⟨pr⟩ => plausRep_implies_plausible R n pr⟩
