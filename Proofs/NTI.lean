import Mathlib.Data.Set.Lattice
set_option linter.style.whitespace false

-- ==========================================
-- Prelim: Definitions
-- ==========================================


variable {A : Type}

-- R represents the stringent implication relation (⇒)
variable (R : A → A → Prop)

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

-- ==========================================
-- Theorem 1: Existence of a Tight Representation
-- ==========================================

-- define canonical structure:

-- The 'R-up-set' w_a
def up_set (a : A) : Set A := { b | R a b }

-- v(a): The states where 'a' is verified
def v (a : A) : Set A := { z | a ∈ up_set R z }

-- f_c(a): The complement of the falsification set f(a)
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

-- The definition of leniency from the paper: `imp` is a leniency of `R`
structure IsLeniency (R imp : A → A → Prop) : Prop where
  L1 : ∀ a b, (∀ c, R c a → up_set R b ⊆ up_set R c) → imp a b
  L2 : ∀ a b c, R a b → imp b c → up_set R c ⊆ up_set R a

-- -------------------------------------------------------
-- Theorem 2, (1) → (2):
-- imp is a leniency implies
-- imp a b ↔ v(a) ⊆ f_c(b) in every tight rep
-- -------------------------------------------------------

/-- Forward (→): given a tight rep, use L2 to pull b's up-set inside c's (where
    c ⇒ a witnesses z ∈ v(a) via T1), then use T2 to conclude z ∈ f_c(b).
    Backward (←): the canonical tight rep exposes the L1 hypothesis directly. -/
theorem leniency_imp_allTightReps (imp : A → A → Prop) :
    IsLeniency R imp →
    ∀ a b, imp a b ↔ ∀ tr : TightRep R, tr.ver a ⊆ tr.fc b := by
  -- constructor
  · intro ⟨hL1, hL2⟩ a b
    constructor
    · -- imp a b → every tight rep has ver(a) ⊆ fc(b)
      intro hab tr z hz
      rw [tr.tight_ver a] at hz
      simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hz
      obtain ⟨c, hca, hzfc⟩ := hz
      -- L2 with R c a and imp a b gives up_set R b ⊆ up_set R c
      have hbc : up_set R b ⊆ up_set R c := hL2 c a b hca hab
      -- Use T2: fc(b) = ⋂_{d ∈ w_b} ver(d); for any d with R b d,
      -- hbc gives R c d, then tr.rep gives z ∈ tr.ver d
      rw [tr.tight_fc b]
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
      exact fun d hbd => (tr.rep c d).mp (hbc hbd) hzfc
    · -- every tight rep has ver(a) ⊆ fc(b) → imp a b
      -- The canonical rep reduces this to the L1 hypothesis
      intro hall
      apply hL1
      -- hall (canonTightRep R) : v R a ⊆ f_c R b
      -- i.e. ∀ c, R c a → up_set R b ⊆ up_set R c  (definitionally)
      exact fun c hca => hall (canonTightRep R) hca

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

/-- Forward (→): the canonical rep (Theorem 1) is the witness;
    L2 with z ∈ v(a) and imp a b directly gives z ∈ f_c(b).
    Backward (←): for L2, chain fc(a) ⊆ ver(b) ⊆ fc(c) ⊆ ver(d) through the
    witnessing rep r to recover R a d from R a b, ver(b)⊆fc(c), and R c d. -/
theorem someRep_imp_leniency (imp : A → A → Prop) :
     (∀ a b, imp a b ↔ ∃ r : Rep R, r.ver a ⊆ r.fc b) →
     IsLeniency R imp := by
  · intro hiff
    constructor
    · -- Recover L1: exhibit the canonical rep as the witness
      -- L1 hypothesis directly gives v R a ⊆ f_c R b for the canonical rep
      intro a b hpush
      apply (hiff a b).mpr
      exact ⟨{ W := A, ver := v R, fc := f_c R, rep := representation_property R },
             fun z hz => hpush z hz⟩
    · -- Recover L2: use the witnessing rep r to chain inclusions
      -- fc(a) ⊆ ver(b) ⊆ fc(c) ⊆ ver(d), so R a d by r.rep
      intro a b c hab himp
      obtain ⟨r, hrep⟩ := (hiff b c).mp himp
      intro d hcd
      exact (r.rep a d).mpr
        (((r.rep a b).mp hab).trans (hrep.trans ((r.rep c d).mp hcd)))

-- ==========================================
-- Theorem 3: Plausibility Characterization
-- ==========================================

/-- The n-down-set m_a^n = {c | n c a} (predecessors of a under n). -/
def down_set (n : A → A → Prop) (a : A) : Set A := { c | n c a }

/-- Membership in down_set unfolds to the relation. -/
private lemma mem_down_set {n : A → A → Prop} {a c : A} :
    c ∈ down_set n a ↔ n c a :=
  Iff.rfl

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
    Leniency is characterized by Theorem 2: n a b iff ver(a) ⊆ fc(b)
    in every tight representation of R. -/
structure IsPlausible (R n : A → A → Prop) : Prop where
  n_refl  : ∀ a, n a a
  n_trans : ∀ {a b c}, n a b → n b c → n a c
  R_le_n  : ∀ a b, R a b → n a b
  n_le    : ∀ a b, n a b → ∀ tr : TightRep R, tr.ver a ⊆ tr.fc b

-- -------------------------------------------------------
-- Theorem 3, Direction (sandwich → plausible):
-- A plausibility representation implies IsPlausible.
-- -------------------------------------------------------

/-- Given a PlausRep, extract plausibility.
    Key steps:
    - n_refl:  tn a ⊆ tn a by reflexivity.
    - n_trans: chain tn a ⊆ tn b ⊆ tn c.
    - R_le_n:  chain tn a ⊆ fc a ⊆ ver b ⊆ tn b using (R) and (P2).
    - n_le:    decompose z ∈ tr.ver a via tight_ver to find c with R c a and
               z ∈ tr.fc c; chain fc c ⊆ ver a ⊆ tn a ⊆ tn b ⊆ fc b ⊆ ver d
               through the PlausRep to obtain R c d; conclude via tr.rep. -/
theorem plausRep_implies_plausible (n : A → A → Prop) (pr : PlausRep R n) :
    IsPlausible R n where
  n_refl a :=
    (pr.sub a a).mpr (subset_refl _)
  n_trans h1 h2 :=
    (pr.sub _ _).mpr (((pr.sub _ _).mp h1).trans ((pr.sub _ _).mp h2))
  R_le_n a b hab :=
    (pr.sub a b).mpr
      ((pr.con a).2.trans (((pr.rep a b).mp hab).trans (pr.con b).1))
  n_le a b hab tr z hz := by
    -- Decompose z ∈ tr.ver a using (T1): get c with R c a and z ∈ tr.fc c
    rw [tr.tight_ver a] at hz
    simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hz
    obtain ⟨c, hca, hzfc⟩ := hz
    -- Suffices to show z ∈ tr.ver d for every d with R b d (by T2)
    rw [tr.tight_fc b]
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    intro d hbd
    -- Chain through PlausRep: fc c ⊆ ver a ⊆ tn a ⊆ tn b ⊆ fc b ⊆ ver d
    -- This gives R c d; then tr.rep c d and z ∈ tr.fc c yields z ∈ tr.ver d.
    have hRcd : R c d := (pr.rep c d).mpr
      (((pr.rep c a).mp hca).trans
        ((pr.con a).1.trans
          (((pr.sub a b).mp hab).trans
            ((pr.con b).2.trans ((pr.rep b d).mp hbd)))))
    exact (tr.rep c d).mp hRcd hzfc

-- -------------------------------------------------------
-- Theorem 3, Direction (plausible → sandwich):
-- IsPlausible yields a canonical PlausRep on state space A ⊕ A.
-- The construction (W̄ = A from the canonical tight rep, A from n-downsets):
--   ver(a) = inl(v̄(a))          ∪ inr(m_a^n)
--   fc(a)  = inl(f̄_c(a))        ∪ inr(m_a^n)
--   tn(a)  = inl(⋃_{c∈m_a^n} v̄(c)) ∪ inr(m_a^n)
-- -------------------------------------------------------

/-- The canonical plausibility representation on state space A ⊕ A. -/
def plausCanonRep (n : A → A → Prop) (hp : IsPlausible R n) : PlausRep R n where
  W   := A ⊕ A
  ver a := Sum.inl '' v R a    ∪ Sum.inr '' down_set n a
  fc  a := Sum.inl '' f_c R a  ∪ Sum.inr '' down_set n a
  tn  a := Sum.inl '' (⋃ c ∈ down_set n a, v R c) ∪ Sum.inr '' down_set n a
  rep := fun a b => by
    constructor
    · -- R a b → fc a ⊆ ver b
      intro hab w hw
      simp only [Set.mem_union, Set.mem_image, mem_down_set] at hw ⊢
      rcases hw with ⟨w', hw'fc, rfl⟩ | ⟨c, hca, rfl⟩
      · -- w = inl w' with w' ∈ f_c R a; by (R), w' ∈ v R b
        exact Or.inl ⟨w', (representation_property R a b).mp hab hw'fc, rfl⟩
      · -- w = inr c with n c a; n c b by transitivity (R a b → n a b)
        exact Or.inr ⟨c, hp.n_trans hca (hp.R_le_n a b hab), rfl⟩
    · -- fc a ⊆ ver b → R a b
      -- Witness inl a ∈ fc a (since a ∈ f_c R a, the identity is in f_c)
      intro hfc
      have hainfc : Sum.inl a ∈ Sum.inl '' f_c R a ∪ Sum.inr '' down_set n a :=
        Or.inl ⟨a, fun _ h => h, rfl⟩
      have hainver := hfc hainfc
      simp only [Set.mem_union, Set.mem_image, mem_down_set] at hainver
      rcases hainver with (⟨w', hw'b, hinl⟩ | ⟨_, _, hinr⟩)
      · -- Sum.inl w' = Sum.inl a implies w' = a; hw'b : a ∈ v R b means R a b
        exact (Sum.inl.inj hinl) ▸ hw'b
      · -- Sum.inr _ = Sum.inl a is a contradiction
        simp at hinr
  sub := fun a b => by
    constructor
    · -- n a b → tn a ⊆ tn b
      intro hab w hw
      simp only [Set.mem_union, Set.mem_image, Set.mem_iUnion, mem_down_set] at hw ⊢
      rcases hw with ⟨w', ⟨c, hca, hw'vc⟩, rfl⟩ | ⟨c, hca, rfl⟩
      · -- w = inl w', ∃ c with n c a and w' ∈ v R c; n c b by transitivity
        exact Or.inl ⟨w', ⟨c, hp.n_trans hca hab, hw'vc⟩, rfl⟩
      · -- w = inr c with n c a; n c b by transitivity
        exact Or.inr ⟨c, hp.n_trans hca hab, rfl⟩
    · -- tn a ⊆ tn b → n a b
      -- Witness inr a ∈ tn a (since n a a by n_refl, so a ∈ m_a^n)
      intro htn
      have haintn : Sum.inr a ∈
          Sum.inl '' (⋃ c ∈ down_set n a, v R c) ∪ Sum.inr '' down_set n a :=
        Or.inr ⟨a, hp.n_refl a, rfl⟩
      have haintnb := htn haintn
      simp only [Set.mem_union, Set.mem_image, Set.mem_iUnion, mem_down_set] at haintnb
      rcases haintnb with (⟨_, _, hinl⟩ | ⟨c, hcb, hinr⟩)
      · -- Sum.inl _ = Sum.inr a is a contradiction
        simp at hinl
      · -- Sum.inr c = Sum.inr a implies c = a; hcb : n c b, so n a b
        exact (Sum.inr.inj hinr) ▸ hcb
  con := fun a => by
    constructor
    · -- ver a ⊆ tn a
      intro w hw
      simp only [Set.mem_union, Set.mem_image, Set.mem_iUnion, mem_down_set] at hw ⊢
      rcases hw with ⟨w', hw'va, rfl⟩ | ⟨c, hca, rfl⟩
      · -- w = inl w' with w' ∈ v R a; put w' in tn a using witness c = a (n a a)
        exact Or.inl ⟨w', ⟨a, hp.n_refl a, hw'va⟩, rfl⟩
      · -- w = inr c with n c a; directly inr c ∈ inr '' m_a^n ⊆ tn a
        exact Or.inr ⟨c, hca, rfl⟩
    · -- tn a ⊆ fc a
      intro w hw
      simp only [Set.mem_union, Set.mem_image, Set.mem_iUnion, mem_down_set] at hw ⊢
      rcases hw with ⟨w', ⟨c, hca, hw'vc⟩, rfl⟩ | ⟨c, hca, rfl⟩
      · -- w = inl w' with n c a and w' ∈ v R c
        -- n_le c a hca on canonical tight rep gives v R c ⊆ f_c R a
        exact Or.inl ⟨w', hp.n_le c a hca (canonTightRep R) hw'vc, rfl⟩
      · -- w = inr c with n c a; directly inr c ∈ inr '' m_a^n ⊆ fc a
        exact Or.inr ⟨c, hca, rfl⟩

/-- Theorem 3 (Plausibility Characterization):
    n is plausible for R iff it admits a plausibility representation. -/
theorem plausibility_characterization (n : A → A → Prop) :
    IsPlausible R n ↔ Nonempty (PlausRep R n) :=
  ⟨fun hp  => ⟨plausCanonRep R n hp⟩,
   fun ⟨pr⟩ => plausRep_implies_plausible R n pr⟩
