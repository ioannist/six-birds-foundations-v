import SixBirdsFoundationsV.Instances.E1ForcingVacuity

namespace SixBirdsFoundationsV.Instances

/-- The forcing obligation is attached to this certificate's actual run family.
Its second field is a local novelty-to-strictness rule, not the infinite
strict-extension conclusion. -/
structure ActualFamilyForcing {C Sigma Entry X Refinement : Type}
    (family : Nat → Option (Entry × (X → Refinement)))
    (challenge : C) (sigma : Nat → Sigma)
    (generic : GenericallyNovelChallenge C Sigma)
    (strict : StrictSelfExtension (X → Refinement) Sigma) where
  recurrent : ∀ n, ∃ t ≥ n, ∃ entry R, family t = some (entry, R)
  freshInstall : ∀ t entry R, family t = some (entry, R) →
    generic.holds challenge (sigma t) → strict.holds R (sigma t)

theorem actualFamilyStrictExtensions {C Sigma Entry X Refinement : Type}
    {family : Nat → Option (Entry × (X → Refinement))}
    {challenge : C} {sigma : Nat → Sigma}
    {generic : GenericallyNovelChallenge C Sigma}
    {strict : StrictSelfExtension (X → Refinement) Sigma}
    (cert : ActualFamilyForcing family challenge sigma generic strict)
    (novel : ∀ t, generic.holds challenge (sigma t)) :
    InfinitelyManyStrictSelfExtensions strict family sigma := by
  intro n
  obtain ⟨t, htn, entry, R, hentry⟩ := cert.recurrent n
  exact ⟨t, entry, R, htn, hentry,
    cert.freshInstall t entry R hentry (novel t)⟩

def periodicTau (n : Nat) : Bool := decide (n % 2 = 0)

theorem periodicTauStep (n : Nat) : periodicTau (n + 1) = !periodicTau n := by
  by_cases h : n % 2 = 0
  · have hn : (n + 1) % 2 ≠ 0 := by omega
    simp [periodicTau, h, hn]
  · have hn : (n + 1) % 2 = 0 := by omega
    simp [periodicTau, h, hn]

def periodicTheory : TheoryPackage Unit Unit Unit Unit where
  Z := Bool
  suppK z z' := z' = !z
  LegitimateStart _ _ := True
  tau := periodicTau
  StepInScope _ := True
  nStart := 0
  f := ()
  Sigma_f := ()
  E := ()
  A := ()
  FormedPackage := True
  formed := trivial

theorem periodicTrajectory (n0 : Nat) :
    OwnKernelTraceTo periodicTheory.LegitimateStart
      periodicTheory.suppK periodicTheory.tau
      periodicTheory.StepInScope 0 n0 := by
  refine ⟨by omega, trivial, ?_⟩
  intro n _ _
  exact ⟨trivial, periodicTauStep n⟩

def periodicPolicy {R : Type} (r : R) : CarriedRecordPolicy periodicTheory R where
  coordinateDeclared f := f = fun _ => r
  rhoOf _ := r

theorem periodicAt {R : Type} (r : R) (n : Nat) :
    CarriedRecordAt (periodicPolicy r) r n .committed_state true true := by
  unfold CarriedRecordAt CarriedRecord IsCarrierCoordinate
    ExistsDeclaredTrajectory CarriedSource periodicPolicy
  exact ⟨rfl, ⟨periodicTrajectory n, rfl⟩,
    ⟨Or.inl rfl, rfl, rfl⟩⟩

theorem periodicCarried {R : Type} (r : R) :
    HasCarriedRecordEvidence (periodicPolicy r) r :=
  ⟨⟨0, .committed_state, true, true, periodicAt r 0⟩⟩

def periodicInstrument : ActiveCarriedInstrument periodicTheory Unit Unit Unit Unit
    Unit Unit (periodicPolicy ()) where
  instrument := SixBirdsIII.baseInstrument
  instrumentRecordCarried _ := True
  recordsAreCompleteInventory := True
  visibilityRecords := []
  thresholdRecords := []
  checkRuleRecords := []
  carried := ⟨trivial, trivial, trivial, trivial⟩
  Detects z _ := z = false
  GateAllows z _ _ := z = false
  ReAudits _ _ z' _ := z' = true

def periodicSystem : ESystem Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit where
  T := periodicTheory
  defectRecordPolicy := periodicPolicy ()
  moveRecordPolicy := periodicPolicy ()
  auditRecordPolicy := periodicPolicy ()
  I_S := periodicInstrument
  Lambda_S := {
    ledgerPolicy := periodicPolicy ()
    ledgerEntries := [()]
    completeLedgerInventory := True
    ledgerComplete := trivial
    ledgerCarried := by intro _ _; exact periodicCarried () }
  R_S := fun _ => {
    sort := ⟨.P1, by decide⟩
    payload := ()
    moveRecord := ()
    moveRecordCarried := periodicCarried ()
    budgetLine := () }
  AdmissibleMove _ z _ _ := z = false

theorem periodicRepair : ESystem.RepairStep periodicSystem false true () () := by
  exact ⟨periodicCarried (), rfl, rfl, rfl,
    by simp [periodicSystem], rfl, rfl, periodicCarried ()⟩

def periodicEntry (t : Nat) : RepairTypedAuditEntry Unit Unit Unit :=
  .move () ⟨t + 1, .committed_state, true, true⟩

def periodicRefinement (t : Nat) : Bool → Nat :=
  fun b => if b then t + 1 else t

def periodicFamily (t : Nat) :
    Option (RepairTypedAuditEntry Unit Unit Unit × (Bool → Nat)) :=
  if t % 2 = 1 then some (periodicEntry t, periodicRefinement t) else none

/-- A clock coordinate lets the system carry a distinct defect at every repair
time and install the corresponding fresh refinement from its move payload. -/
def clockedTheory : TheoryPackage Unit Unit Unit Unit where
  Z := Nat
  suppK z z' := z' = z + 1
  LegitimateStart _ _ := True
  tau := id
  StepInScope _ := True
  nStart := 0
  f := ()
  Sigma_f := ()
  E := ()
  A := ()
  FormedPackage := True
  formed := trivial

theorem clockedTrajectory (n0 : Nat) :
    OwnKernelTraceTo clockedTheory.LegitimateStart clockedTheory.suppK
      clockedTheory.tau clockedTheory.StepInScope 0 n0 := by
  exact ⟨by omega, trivial, by intro n _ _; exact ⟨trivial, rfl⟩⟩

def clockedUnitPolicy : CarriedRecordPolicy clockedTheory Unit where
  coordinateDeclared f := f = fun _ => ()
  rhoOf _ := ()

theorem clockedUnitAt (n : Nat) :
    CarriedRecordAt clockedUnitPolicy () n .committed_state true true := by
  unfold CarriedRecordAt CarriedRecord IsCarrierCoordinate
    ExistsDeclaredTrajectory CarriedSource clockedUnitPolicy
  exact ⟨rfl, ⟨clockedTrajectory n, rfl⟩,
    ⟨Or.inl rfl, rfl, rfl⟩⟩

theorem clockedUnitCarried :
    HasCarriedRecordEvidence clockedUnitPolicy () :=
  ⟨⟨0, .committed_state, true, true, clockedUnitAt 0⟩⟩

def clockedDefectPolicy : CarriedRecordPolicy clockedTheory Nat where
  coordinateDeclared f := f = id
  rhoOf := id

theorem clockedDefectAt (n : Nat) :
    CarriedRecordAt clockedDefectPolicy n n .committed_state true true := by
  unfold CarriedRecordAt CarriedRecord IsCarrierCoordinate
    ExistsDeclaredTrajectory CarriedSource clockedDefectPolicy
  exact ⟨rfl, ⟨clockedTrajectory n, rfl⟩,
    ⟨Or.inl rfl, rfl, rfl⟩⟩

def clockedInstrument : ActiveCarriedInstrument clockedTheory Unit Nat Nat Unit
    Unit Unit clockedUnitPolicy where
  instrument := SixBirdsIII.baseInstrument
  instrumentRecordCarried _ := True
  recordsAreCompleteInventory := True
  visibilityRecords := []
  thresholdRecords := []
  checkRuleRecords := []
  carried := ⟨trivial, trivial, trivial, trivial⟩
  Detects (z : Nat) defect := z % 2 = 1 ∧ defect = z
  GateAllows (z : Nat) defect _ := z % 2 = 1 ∧ defect = z
  ReAudits _ _ (z' : Nat) _ := z' % 2 = 0

def clockedSystem : ESystem Unit Unit Unit Unit Unit Unit Nat Nat Unit Unit where
  T := clockedTheory
  defectRecordPolicy := clockedDefectPolicy
  moveRecordPolicy := clockedUnitPolicy
  auditRecordPolicy := clockedUnitPolicy
  I_S := clockedInstrument
  Lambda_S := {
    ledgerPolicy := clockedUnitPolicy
    ledgerEntries := [()]
    completeLedgerInventory := True
    ledgerComplete := trivial
    ledgerCarried := by intro _ _; exact clockedUnitCarried }
  R_S := fun defect => {
    sort := ⟨.P1, by decide⟩
    payload := defect
    moveRecord := ()
    moveRecordCarried := clockedUnitCarried
    budgetLine := () }
  AdmissibleMove _ (z : Nat) defect move :=
    z % 2 = 1 ∧ defect = z ∧ move.payload = defect

def clockedInstalls : MovePayloadInstallsRefinement Nat (Bool → Nat) where
  holds payload R := R = periodicRefinement payload

def clockedEntry (t : Nat) : RepairTypedAuditEntry Nat Unit Unit :=
  .move () ⟨t + 1, .committed_state, true, true⟩

theorem clockedOddRepair (t : Nat) (ht : t % 2 = 1) :
    ESystem.RepairStep clockedSystem
      t (t + 1) t () ∧
    clockedInstalls.holds (clockedSystem.R_S t).payload
      (periodicRefinement t) ∧
    RepairTypedAuditEntryCarried clockedSystem (clockedEntry t) := by
  have hnext : (t + 1) % 2 = 0 := by omega
  refine ⟨?_, rfl, clockedUnitAt (t + 1)⟩
  exact ⟨⟨t, .committed_state, true, true, clockedDefectAt t⟩,
    ⟨ht, rfl⟩, ⟨ht, rfl⟩, ⟨ht, rfl, rfl⟩,
    by simp [clockedSystem], rfl, hnext, clockedUnitCarried⟩

theorem clockedEvenPerturbation (t : Nat) (ht : t % 2 = 0) :
    t % 2 = 0 ∧
    (t + 1) % 2 = 1 ∧
    clockedTheory.suppK (clockedTheory.tau t)
      (clockedTheory.tau (t + 1)) := by
  have hnext : (t + 1) % 2 = 1 := by omega
  exact ⟨ht, hnext, rfl⟩

theorem periodicOddRepair (t : Nat) (ht : t % 2 = 1) :
    periodicTheory.tau t = false ∧
    periodicTheory.tau (t + 1) = true ∧
    ESystem.RepairStep periodicSystem
      (periodicTheory.tau t) (periodicTheory.tau (t + 1)) () () ∧
    RepairTypedAuditEntryCarried periodicSystem (periodicEntry t) := by
  have hn : (t + 1) % 2 = 0 := by omega
  refine ⟨by simp [periodicTheory, periodicTau, ht],
    by simp [periodicTheory, periodicTau, hn], ?_, ?_⟩
  · simpa [periodicTheory, periodicTau, ht, hn] using periodicRepair
  · exact periodicAt () (t + 1)

theorem periodicEvenPerturbation (t : Nat) (ht : t % 2 = 0) :
    periodicTheory.tau t = true ∧
    periodicTheory.tau (t + 1) = false ∧
    periodicTheory.suppK (periodicTheory.tau t)
      (periodicTheory.tau (t + 1)) := by
  have hn : (t + 1) % 2 ≠ 0 := by omega
  simp [periodicTheory, periodicTau, ht, hn]

theorem periodicFamilyActual (t : Nat) (ht : t % 2 = 1) :
    periodicFamily t = some (periodicEntry t, periodicRefinement t) ∧
    ESystem.RepairStep periodicSystem
      (periodicTheory.tau t) (periodicTheory.tau (t + 1)) () () ∧
    RepairTypedAuditEntryCarried periodicSystem (periodicEntry t) := by
  exact ⟨by simp [periodicFamily, ht],
    (periodicOddRepair t ht).2.2.1, (periodicOddRepair t ht).2.2.2⟩

theorem periodicFamilyEveryEntryExecuted (t : Nat)
    (entry : RepairTypedAuditEntry Unit Unit Unit) (R : Bool → Nat)
    (h : periodicFamily t = some (entry, R)) :
    t % 2 = 1 ∧ entry = periodicEntry t ∧
    R = periodicRefinement t ∧
    ESystem.RepairStep periodicSystem
      (periodicTheory.tau t) (periodicTheory.tau (t + 1)) () () ∧
    RepairTypedAuditEntryCarried periodicSystem entry := by
  have ht : t % 2 = 1 := by
    by_cases ho : t % 2 = 1
    · exact ho
    · simp [periodicFamily, ho] at h
  have hpair : (entry, R) =
      (periodicEntry t, periodicRefinement t) := by
    simpa [periodicFamily, ht] using h.symm
  cases hpair
  exact ⟨ht, rfl, rfl,
    (periodicFamilyActual t ht).2.1,
    (periodicFamilyActual t ht).2.2⟩

def periodicSigma (t : Nat) : Nat × List Nat := (t, List.range t)

def periodicGeneric : GenericallyNovelChallenge Unit (Nat × List Nat) where
  holds _ sigma := sigma.1 ∉ sigma.2

def periodicStrict : StrictSelfExtension (Bool → Nat) (Nat × List Nat) where
  holds R sigma := R false ∉ sigma.2 ∧ R true ≠ R false

theorem periodicNovel (t : Nat) :
    periodicGeneric.holds () (periodicSigma t) := by
  simp [periodicGeneric, periodicSigma, List.mem_range]

theorem periodicStrictAt (t : Nat) :
    periodicStrict.holds (periodicRefinement t) (periodicSigma t) := by
  constructor
  · exact periodicNovel t
  · simp [periodicRefinement]

theorem periodicRefinementsDistinct {t u : Nat} (h : t ≠ u) :
    periodicRefinement t ≠ periodicRefinement u := by
  intro heq
  have hv := congrArg (fun R : Bool → Nat => R false) heq
  simp [periodicRefinement] at hv
  exact h hv

theorem periodicUnbounded (n : Nat) :
    ∃ t ≥ n, ∃ entry R, periodicFamily t = some (entry, R) := by
  let t := 2 * n + 1
  refine ⟨t, by dsimp [t]; omega, periodicEntry t,
    periodicRefinement t, ?_⟩
  have ht : t % 2 = 1 := by dsimp [t]; omega
  exact (periodicFamilyActual t ht).1

def periodicForcing : ActualFamilyForcing periodicFamily () periodicSigma
    periodicGeneric periodicStrict where
  recurrent := periodicUnbounded
  freshInstall := by
    intro t entry R h _
    by_cases ht : t % 2 = 1
    · have hpair : (entry, R) =
          (periodicEntry t, periodicRefinement t) := by
        simpa [periodicFamily, ht] using h.symm
      cases hpair
      exact periodicStrictAt t
    · simp [periodicFamily, ht] at h

theorem periodicStrictExtensions :
    InfinitelyManyStrictSelfExtensions periodicStrict
      periodicFamily periodicSigma :=
  actualFamilyStrictExtensions periodicForcing periodicNovel

def clockedFamily (t : Nat) :
    Option (RepairTypedAuditEntry Nat Unit Unit × (Bool → Nat)) :=
  if t % 2 = 1 then some (clockedEntry t, periodicRefinement t) else none

theorem clockedFamilyActual (t : Nat) (ht : t % 2 = 1) :
    clockedFamily t = some (clockedEntry t, periodicRefinement t) ∧
    ESystem.RepairStep clockedSystem t (t + 1) t () ∧
    clockedInstalls.holds (clockedSystem.R_S t).payload
      (periodicRefinement t) ∧
    RepairTypedAuditEntryCarried clockedSystem (clockedEntry t) := by
  exact ⟨by simp [clockedFamily, ht],
    (clockedOddRepair t ht).1, (clockedOddRepair t ht).2.1,
    (clockedOddRepair t ht).2.2⟩

theorem clockedFamilyEveryEntryInstalled (t : Nat)
    (entry : RepairTypedAuditEntry Nat Unit Unit) (R : Bool → Nat)
    (h : clockedFamily t = some (entry, R)) :
    t % 2 = 1 ∧ entry = clockedEntry t ∧
    R = periodicRefinement t ∧
    ESystem.RepairStep clockedSystem t (t + 1) t () ∧
    clockedInstalls.holds (clockedSystem.R_S t).payload R ∧
    RepairTypedAuditEntryCarried clockedSystem entry := by
  have ht : t % 2 = 1 := by
    by_cases ho : t % 2 = 1
    · exact ho
    · simp [clockedFamily, ho] at h
  have hpair : (entry, R) =
      (clockedEntry t, periodicRefinement t) := by
    simpa [clockedFamily, ht] using h.symm
  cases hpair
  exact ⟨ht, rfl, rfl, (clockedFamilyActual t ht).2.1,
    (clockedFamilyActual t ht).2.2.1,
    (clockedFamilyActual t ht).2.2.2⟩

theorem clockedUnbounded (n : Nat) :
    ∃ t ≥ n, ∃ entry R, clockedFamily t = some (entry, R) := by
  let t := 2 * n + 1
  refine ⟨t, by dsimp [t]; omega, clockedEntry t,
    periodicRefinement t, ?_⟩
  have ht : t % 2 = 1 := by dsimp [t]; omega
  exact (clockedFamilyActual t ht).1

def clockedForcing : ActualFamilyForcing clockedFamily () periodicSigma
    periodicGeneric periodicStrict where
  recurrent := clockedUnbounded
  freshInstall := by
    intro t entry R h _
    have hR := (clockedFamilyEveryEntryInstalled t entry R h).2.2.1
    rw [hR]
    exact periodicStrictAt t

theorem clockedStrictExtensions :
    InfinitelyManyStrictSelfExtensions periodicStrict
      clockedFamily periodicSigma :=
  actualFamilyStrictExtensions clockedForcing periodicNovel

/-- The original `ChallengeHistory` stores a finite list of episodes, so every
episode time in it has a common bound. -/
private theorem episodeTimeBound
    (episodes : List (ChallengeEpisode Unit Unit Unit Unit Unit))
    (episode : ChallengeEpisode Unit Unit Unit Unit Unit)
    (h : episode ∈ episodes) :
    episode.time ≤ episodes.foldr (fun e b => max e.time b) 0 := by
  induction episodes with
  | nil => simp at h
  | cons head tail ih =>
      simp only [List.mem_cons] at h
      simp only [List.foldr_cons]
      rcases h with he | he
      · subst episode
        exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih he) (Nat.le_max_right _ _)

theorem oldHistoryBoundsRepairFamily
    (H : ChallengeHistory Unit Unit Unit Unit Unit Unit Unit Unit)
    (installs : MovePayloadInstallsRefinement Unit (Bool → Nat))
    (postState : PostRepairStateForEpisode periodicSystem Unit Unit Unit Unit Unit)
    (family : Nat → Option (RepairTypedAuditEntry Unit Unit Unit × (Bool → Nat)))
    (actual : ∀ t entry R, family t = some (entry, R) →
      EndogenousRepairOccurrence periodicSystem H installs postState
        () t entry R) :
    ∀ t entry R, family t = some (entry, R) →
      t ≤ H.episodes.foldr (fun e b => max e.time b) 0 := by
  intro t entry R hfamily
  obtain ⟨episode, hmem, _, _, _, htime, _⟩ :=
    actual t entry R hfamily
  simpa [htime] using episodeTimeBound H.episodes episode hmem

theorem noUnboundedOldHistoryFamily
    (H : ChallengeHistory Unit Unit Unit Unit Unit Unit Unit Unit)
    (installs : MovePayloadInstallsRefinement Unit (Bool → Nat))
    (postState : PostRepairStateForEpisode periodicSystem Unit Unit Unit Unit Unit)
    (family : Nat → Option (RepairTypedAuditEntry Unit Unit Unit × (Bool → Nat)))
    (actual : ∀ t entry R, family t = some (entry, R) →
      EndogenousRepairOccurrence periodicSystem H installs postState
        () t entry R)
    (unbounded : ∀ n, ∃ t ≥ n, ∃ entry R, family t = some (entry, R)) : False := by
  let B := H.episodes.foldr (fun e b => max e.time b) 0
  obtain ⟨t, ht, entry, R, hfamily⟩ := unbounded (B + 1)
  have hle := oldHistoryBoundsRepairFamily H installs postState family
    actual t entry R hfamily
  omega

#print axioms actualFamilyStrictExtensions
#print axioms periodicTauStep
#print axioms periodicTrajectory
#print axioms periodicAt
#print axioms periodicCarried
#print axioms periodicRepair
#print axioms periodicOddRepair
#print axioms periodicEvenPerturbation
#print axioms periodicFamilyActual
#print axioms periodicFamilyEveryEntryExecuted
#print axioms periodicNovel
#print axioms periodicStrictAt
#print axioms periodicRefinementsDistinct
#print axioms periodicUnbounded
#print axioms periodicForcing
#print axioms periodicStrictExtensions
#print axioms clockedTrajectory
#print axioms clockedUnitAt
#print axioms clockedUnitCarried
#print axioms clockedDefectAt
#print axioms clockedOddRepair
#print axioms clockedEvenPerturbation
#print axioms clockedFamilyActual
#print axioms clockedFamilyEveryEntryInstalled
#print axioms clockedUnbounded
#print axioms clockedForcing
#print axioms clockedStrictExtensions
#print axioms oldHistoryBoundsRepairFamily
#print axioms episodeTimeBound
#print axioms noUnboundedOldHistoryFamily

end SixBirdsFoundationsV.Instances
