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
