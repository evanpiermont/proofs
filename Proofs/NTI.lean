import Mathlib.Data.Set.Lattice
set_option linter.style.whitespace false

variable {A : Type}
-- R represents the stringent implication relation (⇒) from the paper
variable (R : A → A → Prop)

-- The 'R-up-set' w_a and 'R-down-set' m_a
def up_set (a : A) : Set A := { b | R a b }
def down_set (a : A) : Set A := { b | R b a }

-- v(a): The states where 'a' is verified
def v (a : A) : Set A := { z | a ∈ up_set R z }

-- f_c(a): The complement of the falsification set f(a)
def f_c (a : A) : Set A := { z | up_set R a ⊆ up_set R z }

-- ==========================================
-- Part 1: The Representation Property (R)
-- a ⇒ b if and only if f^c(a) ⊆ v(b)
-- ==========================================
theorem representation_property (a b : A) :
    R a b ↔ f_c R a ⊆ v R b := by
  constructor
  · intro hab z hz
    exact hz hab
  · intro h
    have ha : a ∈ f_c R a := fun x hx => hx
    exact h ha

-- ==========================================
-- Part 2: Tightness Property (T1)
-- v(a) = ⋃_{b ∈ m_a} f^c(b)
-- ==========================================
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

-- ==========================================
-- Part 3: Tightness Property (T2)
-- f^c(a) = ⋂_{b ∈ w_a} v(b)
-- ==========================================
theorem tightness_T2 (a : A) :
    f_c R a = ⋂ b ∈ { x | R a x }, v R b := by
  ext z
  simp [f_c, v, up_set]

-- ==========================================
-- Theorem 1: Existence of a Tight Representation
--
-- Bundles the three components above into a single structure and asserts
-- nonemptiness, so later theorems can invoke it via ⟨canonTightRep R⟩.
-- ==========================================

/-- A tight representation of R on a state space W: maps 'ver' (verification)
    and 'fc' (complement of falsification) satisfying (R), (T1), and (T2). -/
structure TightRep (R : A → A → Prop) where
  W         : Type
  ver       : A → Set W
  fc        : A → Set W
  rep       : ∀ a b, R a b ↔ fc a ⊆ ver b
  tight_ver : ∀ a, ver a = ⋃ b ∈ {x | R x a}, fc b
  tight_fc  : ∀ a, fc a = ⋂ b ∈ {x | R a x}, ver b

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

/-- The canonical leniency relation: a →_R b defined as v(a) ⊆ f_c(b).
    Unfolded: every state that stringently implies a also has b non-falsified.
    This simultaneously defines conditions (2) and (3) of Theorem 2. -/
def leniencyRel : A → A → Prop := fun a b => v R a ⊆ f_c R b

-- -------------------------------------------------------
-- L1 and L2: leniencyRel satisfies the leniency axioms
-- -------------------------------------------------------

/-- L1 (Push axiom): if w_b ⊆ w_c for every c with c ⇒ a, then a →_R b.
    Direct: the hypothesis is exactly the definition of leniencyRel. -/
theorem leniency_L1 (a b : A)
    (h : ∀ c, R c a → up_set R b ⊆ up_set R c) : leniencyRel R a b := by
  intro z hz  -- hz : z ∈ v R a, i.e. R z a (definitionally)
  exact h z hz

/-- L2 (Transitivity axiom): if a ⇒ b and b →_R c, then w_c ⊆ w_a.
    One-liner: a ∈ v R b because R a b, and hbc sends that to a ∈ f_c R c. -/
theorem leniency_L2 (a b c : A)
    (hab : R a b) (hbc : leniencyRel R b c) : up_set R c ⊆ up_set R a :=
  -- v R b = {z | R z b}, so hab : R a b  is definitionally  a ∈ v R b.
  -- hbc then gives a ∈ f_c R c, which is up_set R c ⊆ up_set R a.
  hbc hab

-- -------------------------------------------------------
-- Condition (2) ↔ (1)
-- -------------------------------------------------------

/-- A plain (possibly non-tight) representation of R. -/
structure Rep (R : A → A → Prop) where
  W   : Type
  ver : A → Set W
  fc  : A → Set W
  rep : ∀ a b, R a b ↔ fc a ⊆ ver b

/-- Theorem 2, conditions (1) ↔ (2):
    leniencyRel R a b  iff  ver(a) ⊆ fc(b) in every tight representation of R.

    Forward (→): given any tight rep, expand ver(a) via T1 and fc(b) via T2.
      For z ∈ ⋃_{c ⇒ a} fc(c) and any d with R b d, the chain
        hlab hca : up_set R b ⊆ up_set R c  (applying leniencyRel to c ∈ v R a)
        hlab hca hbd : R c d                (d ∈ up_set R b ⊆ up_set R c)
      then rep gives fc(c) ⊆ ver(d), so z ∈ ver(d).

    Backward (←): instantiate with the canonical tight representation (Theorem 1). -/
theorem leniency_iff_allTightReps (a b : A) :
    leniencyRel R a b ↔ ∀ tr : TightRep R, tr.ver a ⊆ tr.fc b := by
  constructor
  · intro hlab tr z hz
    rw [tr.tight_ver a] at hz
    simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hz
    obtain ⟨c, hca, hzfc⟩ := hz
    rw [tr.tight_fc b]
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    -- hca : R c a  (= c ∈ v R a);  hlab hca : up_set R b ⊆ up_set R c
    -- hbd : R b d  (= d ∈ up_set R b);  hlab hca hbd : R c d
    -- (tr.rep c d).mp _ : tr.fc c ⊆ tr.ver d,  applied to hzfc gives z ∈ tr.ver d
    exact fun d hbd => (tr.rep c d).mp (hlab hca hbd) hzfc
  · -- The canonical tight representation (Theorem 1) is the required witness.
    intro hall
    exact hall (canonTightRep R)

-- -------------------------------------------------------
-- Condition (3) ↔ (1)
-- -------------------------------------------------------

/-- Theorem 2, conditions (1) ↔ (3):
    leniencyRel R a b  iff  ver(a) ⊆ fc(b) in some representation of R.

    Forward (→): the canonical tight representation (Theorem 1) is the witness.

    Backward (←): reconstruct L1 from any representation r with r.ver a ⊆ r.fc b.
      For c with R c a and d with R b d, chain inclusions through r:
        r.fc c ⊆ r.ver a   (by r.rep, from R c a)
               ⊆ r.fc b    (hypothesis hrep)
               ⊆ r.ver d   (by r.rep, from R b d)
      so r.fc c ⊆ r.ver d, giving R c d by r.rep — exactly what L1 needs. -/
theorem leniency_iff_someRep (a b : A) :
    leniencyRel R a b ↔ ∃ r : Rep R, r.ver a ⊆ r.fc b := by
  constructor
  · intro hlab
    -- Canonical tight rep, viewed as a plain rep, witnesses the existential.
    -- Isolate the structure instance to avoid ⟨{...}, ...⟩ parsing errors
    let r_canon : Rep R := {
      W   := A
      ver := v R
      fc  := f_c R
      rep := representation_property R
    }
    exact ⟨r_canon, hlab⟩

  · rintro ⟨r, hrep⟩
    apply leniency_L1
    intro c hca d hbd

    -- Explicitly define the inclusion chain
    have h1 : r.fc c ⊆ r.ver a := (r.rep c a).mp hca
    have h2 : r.ver a ⊆ r.fc b := hrep
    have h3 : r.fc b ⊆ r.ver d := (r.rep b d).mp hbd

    exact (r.rep c d).mpr (fun x hx => h3 (h2 (h1 hx)))
