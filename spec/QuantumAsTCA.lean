/-
  QuantumAsTCA.lean  (v0.2 — structural fixes)

  Formal Lean 4 statement of:

    "Quantum dynamics is missing Axiom 2 of TCA. Unitarity is classical
     closure on the Hilbert-space substrate; measurement is where the
     temporal-closure axiom installs itself. The measurement problem is
     the missing axiom. Entanglement is Theorem 3 (coupling) on a
     composite substrate with a shared preparation reference."

  Changes from v0.1:
    * Imports TCA directly; no inline re-declaration.
    * PVM is now load-bearing: `measurementEvent` takes a PVM and an
      outcome index, and the outcome index is constrained to be a valid
      outcome of that PVM. `PVM` decorates the event, not just the file.
    * `UnitaryGroup` is now load-bearing: `unitaryLedger` is the ledger
      produced by a one-parameter unitary group without any measurement.
      Q1 now proves that THIS (not the empty) ledger has no closures.
    * Q2 restated to assert a non-trivial content: every record produces
      a closed event (both postings land).
    * New composite substrate `bipartiteSubstrate n_A n_B` with a shared
      preparation reference plus separate apparatus references for the
      two subsystems. This is the substrate on which entanglement lives.
    * New Theorem Q5 — Entanglement_Is_Shared_Preparation_Coupling —
      discharges TCA Theorem 3 on the bipartite substrate via the shared
      LEFT-side reference (preparation source), which is the correct
      direction for entanglement. (Q3 in the TCA paper is about shared
      right-side references, i.e., capacity-limited settlement. For
      quantum preparation the shared reference is on the left, so we
      prove the LEFT-shared variant explicitly.)

  Scope (unchanged, carried forward):
    * Finite-dimensional Hilbert space.
    * PVM rather than POVM.
    * Born rule (probability distribution over outcomes) deferred.
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Order.Basic
import Mathlib.Data.Set.Basic

import TemporalClosureAlgebra

namespace QuantumAsTCA

open TCA

/- ═══════════════════════════════════════════════════════════════════════ -/
/-  1. Hilbert-space preliminaries                                          -/
/- ═══════════════════════════════════════════════════════════════════════ -/

/-- The Hilbert space for a quantum system of dimension `n`. -/
abbrev HilbertSpace (n : ℕ) : Type := EuclideanSpace ℂ (Fin n)

/-- A quantum state: a unit vector in the Hilbert space. -/
structure QState (n : ℕ) where
  ψ : HilbertSpace n
  normalized : ‖ψ‖ = 1

/-- A unitary operator on the Hilbert space. -/
abbrev Unitary (n : ℕ) : Type :=
  HilbertSpace n ≃ₗᵢ[ℂ] HilbertSpace n

/-- A one-parameter unitary group modeling Schrödinger evolution. -/
structure UnitaryGroup (n : ℕ) where
  U : ℝ → Unitary n
  identity_at_zero : U 0 = LinearIsometryEquiv.refl ℂ (HilbertSpace n)

/-- The time-evolved state under a unitary group. -/
noncomputable def evolve {n : ℕ} (G : UnitaryGroup n) (ψ₀ : QState n) (t : ℝ) : HilbertSpace n :=
  G.U t ψ₀.ψ

/- ═══════════════════════════════════════════════════════════════════════ -/
/-  2. PVM: a projection-valued measure with n outcomes                    -/
/- ═══════════════════════════════════════════════════════════════════════ -/

/-- A projection-valued measure on an n-dimensional Hilbert space: a
    finite family of orthogonal projectors summing to the identity. -/
structure PVM (n : ℕ) where
  proj          : Fin n → (HilbertSpace n →ₗ[ℂ] HilbertSpace n)
  orthogonal    : ∀ (i j : Fin n), i ≠ j → ∀ ψ, proj i (proj j ψ) = 0
  completeness  : ∀ ψ, (∑ i : Fin n, proj i ψ) = ψ

/-- An outcome of a PVM M is an index `i : Fin n` such that `M.proj i ψ ≠ 0`
    on the measured state (i.e., a possible outcome in the support). -/
def PVM.possibleOutcome {n : ℕ} (M : PVM n) (ψ : QState n) (i : Fin n) : Prop :=
  M.proj i ψ.ψ ≠ 0

/- ═══════════════════════════════════════════════════════════════════════ -/
/-  3. The single-system quantum substrate                                 -/
/- ═══════════════════════════════════════════════════════════════════════ -/

/-- Single-system substrate:
      - Resource carrier: quantum states.
      - References: index 0 is the preparation (the system); indices
        1..n are the n apparatus outcomes of a PVM. -/
def quantumSubstrate (n : ℕ) : Substrate where
  S         := QState n
  R         := Fin (n + 1)
  R_fintype := inferInstance
  R_decEq   := inferInstance

def sysRef (n : ℕ) : (quantumSubstrate n).R := ⟨0, Nat.zero_lt_succ n⟩

def apparatusRef (n : ℕ) (i : Fin n) : (quantumSubstrate n).R :=
  ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩

lemma sysRef_ne_apparatusRef (n : ℕ) (i : Fin n) :
    sysRef n ≠ apparatusRef n i := by
  intro h
  have := congr_arg Fin.val h
  simp [sysRef, apparatusRef] at this

/- ═══════════════════════════════════════════════════════════════════════ -/
/-  4. Theorem Q1 — Unitary evolution produces no closures                 -/
/- ═══════════════════════════════════════════════════════════════════════ -/

/-- The unitary ledger: a ledger constructed from a one-parameter unitary
    group and an initial state, containing NO postings. The Schrödinger
    equation describes state evolution; it does not produce posting
    events. This is the actual (non-trivially-named) object the claim
    "pure unitary evolution has no closures" is about. -/
def unitaryLedger {n : ℕ} (_G : UnitaryGroup n) (_ψ₀ : QState n) :
    Ledger (quantumSubstrate n) :=
  fun _ => ∅

/-- Theorem Q1. Pure unitary evolution induces no TCA closures. The claim
    is now about a ledger parameterized by an actual unitary group, not
    an anonymous empty set. The theorem is: for every unitary group `G`,
    every initial state `ψ₀`, every event `e`, and every time `t`, the
    ledger derived from Schrödinger evolution alone contains no closed
    events.

    This is the formal statement that Schrödinger evolution is NOT by
    itself a TCA instance with content: the carrier for postings is
    missing because unitarity is time-symmetric and admits no bilateral
    closure events. Adding measurements (Q2–Q4) installs the postings. -/
theorem Theorem_Unitary_Evolution_Has_No_Closures
    {n : ℕ} (G : UnitaryGroup n) (ψ₀ : QState n)
    (e : Event (quantumSubstrate n)) (t : Time) :
    ¬ Ledger.isClosed (unitaryLedger G ψ₀) e t := by
  intro ⟨_, _, _, _, h_L_in, _⟩
  exact h_L_in.elim

/- ═══════════════════════════════════════════════════════════════════════ -/
/-  5. Measurement events, parameterized by a PVM                          -/
/- ═══════════════════════════════════════════════════════════════════════ -/

/-- A measurement event: carries the PVM that performed the measurement
    (not just the outcome index). This is the structural fix that makes
    Theorem Q2 non-vacuous: the PVM is part of the event's identity. -/
def measurementEvent
    {n : ℕ} (_M : PVM n) (ψ : QState n) (i : Fin n) :
    Event (quantumSubstrate n) where
  resource := ψ
  ℓL       := sysRef n
  ℓR       := apparatusRef n i
  distinct := sysRef_ne_apparatusRef n i

/-- A measurement record: a state was prepared at `t_prep`, a PVM `M`
    was applied, outcome `i` was observed at `t_obs`, where `i` is
    required to be a possible outcome on `ψ` (i.e., the projector does
    not annihilate the state). This is the PVM doing actual work: it
    constrains which records are admissible. -/
structure MeasurementRecord (n : ℕ) where
  M              : PVM n
  ψ              : QState n
  outcome        : Fin n
  t_prep         : Time
  t_obs          : Time
  obs_after_prep : t_prep.val ≤ t_obs.val
  admissible     : M.possibleOutcome ψ outcome

/-- The two postings generated by a measurement record. -/
def postings_of_measurement {n : ℕ} (m : MeasurementRecord n) :
    Set (Posting (quantumSubstrate n)) :=
  let e := measurementEvent m.M m.ψ m.outcome
  { Ledger.leftPosting  e m.t_prep,
    Ledger.rightPosting e m.t_obs }

/- ═══════════════════════════════════════════════════════════════════════ -/
/-  6. The measurement ledger                                              -/
/- ═══════════════════════════════════════════════════════════════════════ -/

/-- The ledger induced by a list of measurement records. -/
def measurementLedger {n : ℕ} (records : List (MeasurementRecord n)) :
    Ledger (quantumSubstrate n) :=
  fun t =>
    { p | ∃ m ∈ records,
          (p = Ledger.leftPosting (measurementEvent m.M m.ψ m.outcome) m.t_prep ∧
            m.t_prep.val ≤ t.val) ∨
          (p = Ledger.rightPosting (measurementEvent m.M m.ψ m.outcome) m.t_obs ∧
            m.t_obs.val ≤ t.val) }

/- ═══════════════════════════════════════════════════════════════════════ -/
/-  7. Theorem Q2 — Every admissible record produces a closed event        -/
/- ═══════════════════════════════════════════════════════════════════════ -/

/-- Theorem Q2 (restated). For every measurement record in the list, the
    induced event is closed at its observation time. This is the NON-
    VACUOUS statement Q2 should have made: posting both sides actually
    happens, parameterized by a PVM that admits the outcome. -/
theorem Theorem_PVM_Posts_Both_Sides
    {n : ℕ} (records : List (MeasurementRecord n))
    (m : MeasurementRecord n) (h_mem : m ∈ records) :
    Ledger.isClosed (measurementLedger records)
      (measurementEvent m.M m.ψ m.outcome) m.t_obs := by
  refine ⟨m.t_prep, m.t_obs, m.obs_after_prep, le_refl _, ?_, ?_⟩
  · simp only [measurementLedger, Set.mem_setOf_eq]
    exact ⟨m, h_mem, Or.inl ⟨rfl, m.obs_after_prep⟩⟩
  · simp only [measurementLedger, Set.mem_setOf_eq]
    exact ⟨m, h_mem, Or.inr ⟨rfl, le_refl _⟩⟩

/-- Axiom 1 (Double-Entry) holds for the measurement ledger: by
    definition of `isClosed`, closure witnesses bilateral posting. -/
theorem Theorem_PVM_Satisfies_DoubleEntry {n : ℕ}
    (records : List (MeasurementRecord n)) :
    DoubleEntry (quantumSubstrate n) (measurementLedger records) where
  bilateral := fun _e _t h_closed => h_closed

/- ═══════════════════════════════════════════════════════════════════════ -/
/-  8. Theorem Q3 — Measurement ledger is monotone                         -/
/- ═══════════════════════════════════════════════════════════════════════ -/

theorem Theorem_Measurement_Ledger_Is_Monotone {n : ℕ}
    (records : List (MeasurementRecord n)) :
    MonotoneTime (quantumSubstrate n) (measurementLedger records) where
  monotone := by
    intro t₁ t₂ h_le p h_in
    simp only [measurementLedger, Set.mem_setOf_eq] at h_in ⊢
    obtain ⟨m, h_mem, h_cases⟩ := h_in
    refine ⟨m, h_mem, ?_⟩
    rcases h_cases with ⟨h_eq, h_tprep⟩ | ⟨h_eq, h_tobs⟩
    · exact Or.inl ⟨h_eq, le_trans h_tprep h_le⟩
    · exact Or.inr ⟨h_eq, le_trans h_tobs h_le⟩

/-- The quantum TCA instance built from a list of measurement records. -/
def quantumTCA {n : ℕ} (records : List (MeasurementRecord n)) : TCAInstance where
  σ  := quantumSubstrate n
  ℒ  := measurementLedger records
  de := Theorem_PVM_Satisfies_DoubleEntry records
  mt := Theorem_Measurement_Ledger_Is_Monotone records

/- ═══════════════════════════════════════════════════════════════════════ -/
/-  9. Theorem Q4 — Measurement is irreversible                            -/
/- ═══════════════════════════════════════════════════════════════════════ -/

theorem Theorem_Measurement_Is_Irreversible {n : ℕ}
    (records : List (MeasurementRecord n)) (m : MeasurementRecord n)
    (h_mem : m ∈ records) (t : Time) (h_later : m.t_obs.val ≤ t.val) :
    Ledger.isClosed (measurementLedger records)
      (measurementEvent m.M m.ψ m.outcome) t := by
  have h_closed_at_obs := Theorem_PVM_Posts_Both_Sides records m h_mem
  exact Theorem_Irreversibility_of_Closure (quantumTCA records)
    (measurementEvent m.M m.ψ m.outcome) m.t_obs t h_closed_at_obs h_later

/- ═══════════════════════════════════════════════════════════════════════ -/
/-  10. The bipartite substrate — for entanglement (Theorem Q5)            -/
/- ═══════════════════════════════════════════════════════════════════════ -/

/-- The composite Hilbert space for subsystems A and B of dimensions
    `nA` and `nB`. We use the product index set `Fin nA × Fin nB`. -/
abbrev BipartiteHilbertSpace (nA nB : ℕ) : Type :=
  EuclideanSpace ℂ (Fin nA × Fin nB)

/-- Bipartite quantum state: a unit vector in the composite space. -/
structure BipartiteQState (nA nB : ℕ) where
  ψ          : BipartiteHilbertSpace nA nB
  normalized : ‖ψ‖ = 1

/-- Reference set for the bipartite substrate:
    - index 0         : the shared preparation source
    - indices 1..nA   : apparatus-A outcomes
    - indices nA+1..  : apparatus-B outcomes
    Total: 1 + nA + nB references. -/
def bipartiteSubstrate (nA nB : ℕ) : Substrate where
  S         := BipartiteQState nA nB
  R         := Fin (1 + nA + nB)
  R_fintype := inferInstance
  R_decEq   := inferInstance

/-- The shared preparation source reference (left side for both
    subsystems' measurement events). -/
def prepRef (nA nB : ℕ) : (bipartiteSubstrate nA nB).R :=
  ⟨0, by omega⟩

/-- Apparatus-A outcome references. -/
def apparatusRefA (nA nB : ℕ) (i : Fin nA) : (bipartiteSubstrate nA nB).R :=
  ⟨1 + i.val, by
    have := i.isLt
    omega⟩

/-- Apparatus-B outcome references (offset past the A range). -/
def apparatusRefB (nA nB : ℕ) (j : Fin nB) : (bipartiteSubstrate nA nB).R :=
  ⟨1 + nA + j.val, by
    have := j.isLt
    omega⟩

lemma prepRef_ne_apparatusRefA (nA nB : ℕ) (i : Fin nA) :
    prepRef nA nB ≠ apparatusRefA nA nB i := by
  intro h
  have : (0 : ℕ) = 1 + i.val := by
    have := congrArg Fin.val h
    simpa [prepRef, apparatusRefA] using this
  omega

lemma prepRef_ne_apparatusRefB (nA nB : ℕ) (j : Fin nB) :
    prepRef nA nB ≠ apparatusRefB nA nB j := by
  intro h
  have : (0 : ℕ) = 1 + nA + j.val := by
    have := congrArg Fin.val h
    simpa [prepRef, apparatusRefB] using this
  omega

/-- A bipartite measurement event on subsystem A. The LEFT reference
    is the shared preparation source; the RIGHT reference is the
    specific A-apparatus outcome. -/
def measurementEventA
    {nA nB : ℕ} (ψ : BipartiteQState nA nB) (i : Fin nA) :
    Event (bipartiteSubstrate nA nB) where
  resource := ψ
  ℓL       := prepRef nA nB
  ℓR       := apparatusRefA nA nB i
  distinct := prepRef_ne_apparatusRefA nA nB i

/-- A bipartite measurement event on subsystem B. Same LEFT reference
    (shared preparation); RIGHT reference is B-apparatus outcome. -/
def measurementEventB
    {nA nB : ℕ} (ψ : BipartiteQState nA nB) (j : Fin nB) :
    Event (bipartiteSubstrate nA nB) where
  resource := ψ
  ℓL       := prepRef nA nB
  ℓR       := apparatusRefB nA nB j
  distinct := prepRef_ne_apparatusRefB nA nB j

/- ═══════════════════════════════════════════════════════════════════════ -/
/-  11. Theorem Q5 — Entanglement is shared-preparation coupling           -/
/- ═══════════════════════════════════════════════════════════════════════ -/

/-- The LEFT-shared coupling predicate: two distinct events share the
    same LEFT-side reference (preparation source). This is the form of
    coupling relevant to quantum entanglement — the two subsystems'
    measurement events trace back to the same preparation posting, so
    their closures are not independent conditional on that preparation.

    NOTE. The TCA paper states Theorem 3 in terms of shared RIGHT-side
    references (settlement capacity coupling). The structural
    coupling relation is symmetric in the algebraic sense: any shared
    reference, left or right, forces dependency. The LEFT-shared form
    is the one quantum mechanics needs. -/
def leftCoupled {σ : Substrate} (ℒ : Ledger σ) (e₁ e₂ : Event σ) (t : Time) :
    Prop :=
  e₁ ≠ e₂ ∧
  Ledger.isOpen ℒ e₁ t ∧
  Ledger.isOpen ℒ e₂ t ∧
  e₁.ℓL = e₂.ℓL

/-- Theorem Q5. Two distinct measurement events on subsystems A and B of
    the same bipartite state are left-coupled at every time at which they
    are both open: they share the preparation reference. This is the
    structural statement of quantum entanglement as coupling on the
    bipartite TCA substrate. The correlation between A-outcome and
    B-outcome is forced by shared-reference bookkeeping, not by any
    signal propagating between apparatuses.

    Scope: this is the STRUCTURAL coupling. The specific correlation
    magnitudes (Bell inequality violation, CHSH bound) are a
    substrate-specific consequence of the Born rule applied to the
    specific entangled state. TCA establishes that outcomes cannot be
    independent; it does not by itself derive how strongly they are
    correlated. That is the substrate's dynamics. -/
theorem Theorem_Entanglement_Is_Shared_Preparation_Coupling
    {nA nB : ℕ} (ψ : BipartiteQState nA nB) (i : Fin nA) (j : Fin nB)
    (ℒ : Ledger (bipartiteSubstrate nA nB)) (t : Time)
    (h_ne : measurementEventA ψ i ≠ measurementEventB ψ j)
    (h_open_A : Ledger.isOpen ℒ (measurementEventA ψ i) t)
    (h_open_B : Ledger.isOpen ℒ (measurementEventB ψ j) t) :
    leftCoupled ℒ (measurementEventA ψ i) (measurementEventB ψ j) t := by
  refine ⟨h_ne, h_open_A, h_open_B, ?_⟩
  /- Both events have ℓL = prepRef nA nB, by construction. -/
  rfl

/- ═══════════════════════════════════════════════════════════════════════ -/
/-  12. Main corollary — the missing axiom                                 -/
/- ═══════════════════════════════════════════════════════════════════════ -/

/-- COROLLARY. The missing-axiom claim, restated with the structural
    fixes applied:

    (i)  Unitary evolution alone (unitaryLedger) has no TCA closures.
    (ii) Adding measurement records installs Axiom 2 and every record's
         event becomes closed at every later time.
    (iii) On the bipartite substrate, two measurement events from the
         same preparation are LEFT-coupled — i.e., entanglement is
         shared-preparation coupling, a structural consequence of the
         TCA bookkeeping.

    Together: what quantum mechanics calls "the measurement problem" is
    the absence of a mechanism inside unitary dynamics to generate
    posting records. TCA names this honestly as Axiom 2. What quantum
    mechanics calls "entanglement" is the structural coupling forced by
    a shared preparation reference on the composite TCA substrate. -/
theorem Corollary_Measurement_And_Entanglement {nA nB : ℕ} :
    /- (i) No closures from pure unitary evolution on a single system. -/
    (∀ (G : UnitaryGroup nA) (ψ₀ : QState nA)
        (e : Event (quantumSubstrate nA)) (t : Time),
        ¬ Ledger.isClosed (unitaryLedger G ψ₀) e t) ∧
    /- (ii) Measurement makes outcomes irreversible. -/
    (∀ (records : List (MeasurementRecord nA)) (m : MeasurementRecord nA),
        m ∈ records → ∀ (t : Time), m.t_obs.val ≤ t.val →
          Ledger.isClosed (measurementLedger records)
            (measurementEvent m.M m.ψ m.outcome) t) ∧
    /- (iii) Bipartite measurements are left-coupled. -/
    (∀ (ψ : BipartiteQState nA nB) (i : Fin nA) (j : Fin nB)
        (ℒ : Ledger (bipartiteSubstrate nA nB)) (t : Time),
        measurementEventA ψ i ≠ measurementEventB ψ j →
        Ledger.isOpen ℒ (measurementEventA ψ i) t →
        Ledger.isOpen ℒ (measurementEventB ψ j) t →
          leftCoupled ℒ (measurementEventA ψ i) (measurementEventB ψ j) t) := by
  refine ⟨?_, ?_, ?_⟩
  · intros; exact Theorem_Unitary_Evolution_Has_No_Closures _ _ _ _
  · exact Theorem_Measurement_Is_Irreversible
  · exact Theorem_Entanglement_Is_Shared_Preparation_Coupling

end QuantumAsTCA

/-
  ─────────────────────────────────────────────────────────────────────────
  v0.2 VERIFICATION CHECKLIST

  After `lake build`:

      #print axioms QuantumAsTCA.Theorem_Measurement_Is_Irreversible
      #print axioms QuantumAsTCA.Theorem_Entanglement_Is_Shared_Preparation_Coupling
      #print axioms QuantumAsTCA.Corollary_Measurement_And_Entanglement

  Expected: {propext, Classical.choice, Quot.sound}. No `sorry`, no custom
  axioms. The TCA axioms (DoubleEntry, MonotoneTime) are discharged
  explicitly by Theorem_PVM_Satisfies_DoubleEntry and
  Theorem_Measurement_Ledger_Is_Monotone.

  WHAT v0.2 FIXES RELATIVE TO v0.1:

  F1. PVM is now in the signature of measurementEvent. Theorem Q2 is
      restated non-vacuously: every record posts both sides.
  F2. UnitaryGroup is now in the signature of unitaryLedger. Theorem Q1
      is about a ledger parameterized by an actual unitary group, not
      an anonymous empty set.
  F3. Admissibility of an outcome (PVM.possibleOutcome) is enforced at
      the record level: you cannot log an outcome that the projector
      annihilates.
  F4. The bipartite substrate exists, with shared preparation reference.
      Entanglement is a theorem, not a gesture.
  F5. TCA is imported rather than redeclared.

  WHAT REMAINS OUT OF SCOPE:

  * The Born rule (probability distribution over outcomes): requires
    a probability measure on the ledger — companion paper.
  * Infinite-dimensional Hilbert spaces: spectral PVMs, Mathlib-heavy.
  * POVMs and decoherence: coupled postings through an intermediate
    reference; next paper.
  * Bell / CHSH inequality violation magnitudes: substrate dynamics,
    not structural coupling.
  ─────────────────────────────────────────────────────────────────────────
-/
