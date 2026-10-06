import SixBirdsFoundationsV.Laws.E12Individuation

namespace SixBirdsFoundationsV.Instances

/- A two-state device: false is perturbed, and its installed repair moves to true. -/
def spikeTheory : TheoryPackage Unit Unit Unit Unit where
  Z := Bool
  suppK _ z' := z' = true
  LegitimateStart _ _ := True
  tau _ := true
  StepInScope _ := True
  nStart := 0
  f := ()
  Sigma_f := ()
  E := ()
  A := ()
  FormedPackage := True
  formed := trivial

def spikePolicy {R : Type} (r : R) : CarriedRecordPolicy spikeTheory R where
  coordinateDeclared f := f = fun _ => r
  rhoOf _ := r

theorem spikeAt {R : Type} (r : R) :
    CarriedRecordAt (spikePolicy r) r 0 .committed_state true true := by
  unfold CarriedRecordAt CarriedRecord IsCarrierCoordinate
    ExistsDeclaredTrajectory OwnKernelTraceTo CarriedSource spikePolicy
  exact ⟨rfl, ⟨⟨Nat.le_refl 0, trivial, by intro n _ h; omega⟩, rfl⟩,
    ⟨Or.inl rfl, rfl, rfl⟩⟩

theorem spikeCarried {R : Type} (r : R) :
    HasCarriedRecordEvidence (spikePolicy r) r :=
  ⟨⟨0, .committed_state, true, true, spikeAt r⟩⟩

def spikeInstrument : ActiveCarriedInstrument spikeTheory Unit Unit Unit Unit
    Unit Unit (spikePolicy ()) where
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

def spikeSystem : ESystem Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit where
  T := spikeTheory
  defectRecordPolicy := spikePolicy ()
  moveRecordPolicy := spikePolicy ()
  auditRecordPolicy := spikePolicy ()
  I_S := spikeInstrument
  Lambda_S := {
    ledgerPolicy := spikePolicy ()
    ledgerEntries := [()]
    completeLedgerInventory := True
    ledgerComplete := trivial
    ledgerCarried := by intro _ _; exact spikeCarried () }
  R_S := fun _ => {
    sort := ⟨.P1, by decide⟩
    payload := ()
    moveRecord := ()
    moveRecordCarried := spikeCarried ()
    budgetLine := () }
  AdmissibleMove _ z _ _ := z = false

theorem spikeRepair : ESystem.RepairStep spikeSystem false true () () := by
  refine ⟨spikeCarried (), rfl, rfl, rfl, by simp [spikeSystem], rfl,
    rfl, spikeCarried ()⟩

/- A carried level can be reindexed without changing any counted records. -/
def spikeLevel (n : Nat) : CarriedInstrumentLevel spikeSystem where
  levelIndex := n
  levelTag := n
  instrument := spikeInstrument
  levelRecord := ()
  auditsLowerStack := fun _ => True
  lowerStackTarget := []
  usedLedgerEntries := []
  usedAuditRecords := []

theorem spikeLevelOccurs (n : Nat) :
    CarriedInstrumentLevelOccurrence spikeSystem (spikeLevel n) := by
  exact ⟨trivial, spikeInstrument.carried, trivial,
    (by intro e h; cases h), (by intro a h; cases h),
    (by intro k h; cases h)⟩

theorem spikeNoE2 (measure : AuditTowerCapacityMeasure spikeSystem) : False := by
  have h0 := measure.countsOnlyCarriedRecords (spikeLevel 0) (spikeLevelOccurs 0)
    (measure.instrumentRecordId ())
  have h1 := measure.countsOnlyCarriedRecords (spikeLevel 1) (spikeLevelOccurs 1)
    (measure.instrumentRecordId ())
  have hm0 : measure.instrumentRecordId () ∈
      (measure.levelRecordSet (spikeLevel 0)).records :=
    h0.mpr (Or.inl rfl)
  have hm1 : measure.instrumentRecordId () ∈
      (measure.levelRecordSet (spikeLevel 1)).records :=
    h1.mpr (Or.inl rfl)
  exact measure.disjointAcrossLevels (spikeLevel 0) (spikeLevel 1)
    (spikeLevelOccurs 0) (spikeLevelOccurs 1) (by decide)
    (measure.instrumentRecordId ()) hm0 hm1

theorem noE2WithOccurringLevel
    {F R E A I L D P M U : Type}
    (S : ESystem F R E A I L D P M U)
    (level : CarriedInstrumentLevel S)
    (occurs : CarriedInstrumentLevelOccurrence S level)
    (measure : AuditTowerCapacityMeasure S) : False := by
  let other : CarriedInstrumentLevel S :=
    { levelIndex := level.levelIndex + 1
      levelTag := level.levelTag
      instrument := level.instrument
      levelRecord := level.levelRecord
      auditsLowerStack := level.auditsLowerStack
      lowerStackTarget := []
      usedLedgerEntries := level.usedLedgerEntries
      usedAuditRecords := level.usedAuditRecords }
  have otherOccurs : CarriedInstrumentLevelOccurrence S other := by
    rcases occurs with ⟨hrecord, hinst, hsystem, hledger, haudit, _⟩
    exact ⟨hrecord, hinst, hsystem, hledger, haudit,
      by intro k h; cases h⟩
  have hleft := measure.countsOnlyCarriedRecords level occurs
    (measure.instrumentRecordId level.levelRecord)
  have hright := measure.countsOnlyCarriedRecords other otherOccurs
    (measure.instrumentRecordId level.levelRecord)
  have hmleft := hleft.mpr (Or.inl rfl)
  have hmright := hright.mpr (Or.inl rfl)
  exact measure.disjointAcrossLevels level other occurs otherOccurs
    (by simp [other]) (measure.instrumentRecordId level.levelRecord)
    hmleft hmright

def spikeApp (n : Nat) : ClosureApparatus spikeSystem where
  time := n
  gateInstrument := spikeInstrument
  thresholdRecords := []
  appBoundary := ⟨0⟩
  auditData := ⟨0⟩
  apparatusRecord := ⟨0⟩
  usedLedgerEntries := []
  usedAuditRecords := []

def spikeMaintenance : ClosureMaintenanceOperator spikeSystem where
  operatorRecord := ⟨0⟩
  apply _ := spikeApp 1
  operatorLedgerEntries := [()]
  operatorAuditRecords := [()]

def spikeReinstatement : MaintenanceReinstatementRecord spikeSystem where
  time := 0
  sourceState := false
  targetState := true
  operatorRecord := spikeMaintenance.operatorRecord
  preAppRecord := (spikeApp 0).apparatusRecord
  postAppRecord := (spikeApp 1).apparatusRecord
  outputRecord := (spikeApp 1).apparatusRecord
  reinstatementLedgerEntry := ()

theorem spikeAppOccurs (n : Nat) :
    ClosureApparatusOccurrenceFor spikeSystem (spikePolicy ⟨0⟩)
      n (spikeApp n) := by
  refine ⟨rfl, ?_, spikeInstrument.carried, ?_, ?_, ?_⟩
  · exact ⟨0, .committed_state, true, true,
      spikeAt (ClosureApparatusRecord.mk 0)⟩
  · intro r h; cases h
  · intro e h; cases h
  · intro a h; cases h

theorem spikeMaintenanceOccurs :
    MaintenanceOperatorOccurrenceFor spikeSystem (spikePolicy ⟨0⟩)
      0 spikeMaintenance := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨0, .committed_state, true, true,
      spikeAt (MaintenanceOperatorRecord.mk 0), Or.inl rfl, rfl, rfl⟩
  · intro e h; cases e; simp [spikeSystem]
  · intro a h; exact spikeCarried ()

theorem spikeE3Reinstatement
    (H : ChallengeHistory Unit Unit Unit Unit Unit Unit Unit Unit) :
    MaintenanceReinstatementFor spikeSystem H (spikePolicy ⟨0⟩)
      (spikePolicy ⟨0⟩) (spikePolicy spikeReinstatement)
      0 (spikeApp 0) (spikeApp 1) spikeMaintenance spikeReinstatement := by
  refine ⟨spikeAppOccurs 0, spikeAppOccurs 1, spikeMaintenanceOccurs, ?_⟩
  refine ⟨0, .committed_state, true, true,
    spikeAt spikeReinstatement, Or.inl rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    ?_, rfl⟩
  simp [spikeSystem]

def spikeBoundary : BoundaryApparatusFor spikeSystem where
  holds := fun _ app => app.apparatusRecord.recordId = 0

theorem spikeSelfMaintained
    (H : ChallengeHistory Unit Unit Unit Unit Unit Unit Unit Unit)
    (B : InstitutionalBoundaryCandidate (T := spikeTheory) (fun _ => True)) :
    SelfMaintainedBoundary spikeSystem H (spikePolicy ⟨0⟩)
      (spikePolicy ⟨0⟩) (spikePolicy spikeReinstatement)
      spikeBoundary (fun _ => True) B := by
  exact ⟨0, spikeApp 0, spikeApp 1, spikeMaintenance,
    spikeReinstatement, rfl, spikeE3Reinstatement H, trivial⟩

#print axioms spikeAt
#print axioms spikeCarried
#print axioms spikeRepair
#print axioms spikeLevelOccurs
#print axioms spikeNoE2
#print axioms noE2WithOccurringLevel
#print axioms spikeAppOccurs
#print axioms spikeMaintenanceOccurs
#print axioms spikeE3Reinstatement
#print axioms spikeSelfMaintained

end SixBirdsFoundationsV.Instances
