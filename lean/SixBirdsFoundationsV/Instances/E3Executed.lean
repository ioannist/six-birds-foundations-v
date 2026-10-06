import SixBirdsFoundationsV.Instances.E3Episode

namespace SixBirdsFoundationsV.Instances

/-- The repair occurs between the declared states at times zero and one. -/
def eventTheory : TheoryPackage Unit Unit Unit Unit where
  Z := Bool
  suppK z z' := (z = false ∧ z' = true) ∨ (z = true ∧ z' = true)
  LegitimateStart _ _ := True
  tau n := n ≠ 0
  StepInScope _ := True
  nStart := 0
  f := ()
  Sigma_f := ()
  E := ()
  A := ()
  FormedPackage := True
  formed := trivial

theorem eventTrajectory :
    OwnKernelTraceTo eventTheory.LegitimateStart eventTheory.suppK
      eventTheory.tau eventTheory.StepInScope 0 1 := by
  refine ⟨by omega, trivial, ?_⟩
  intro n hn hlt
  have h : n = 0 := by omega
  subst n
  exact ⟨trivial, Or.inl ⟨rfl, rfl⟩⟩

theorem eventTransition :
    eventTheory.tau 0 = false ∧ eventTheory.tau 1 = true ∧
      eventTheory.suppK (eventTheory.tau 0) (eventTheory.tau 1) := by
  exact ⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩

def eventPolicy {R : Type} (r : R) : CarriedRecordPolicy eventTheory R where
  coordinateDeclared f := f = fun _ => r
  rhoOf _ := r

theorem eventAt {R : Type} (r : R) :
    CarriedRecordAt (eventPolicy r) r 1 .committed_state true true := by
  unfold CarriedRecordAt CarriedRecord IsCarrierCoordinate
    ExistsDeclaredTrajectory CarriedSource eventPolicy
  exact ⟨rfl, ⟨eventTrajectory, rfl⟩, ⟨Or.inl rfl, rfl, rfl⟩⟩

theorem eventCarried {R : Type} (r : R) :
    HasCarriedRecordEvidence (eventPolicy r) r :=
  ⟨⟨1, .committed_state, true, true, eventAt r⟩⟩

def eventInstrument : ActiveCarriedInstrument eventTheory Unit Unit Unit Unit
    Unit Unit (eventPolicy ()) where
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

def eventSystem : ESystem Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit where
  T := eventTheory
  defectRecordPolicy := eventPolicy ()
  moveRecordPolicy := eventPolicy ()
  auditRecordPolicy := eventPolicy ()
  I_S := eventInstrument
  Lambda_S := {
    ledgerPolicy := eventPolicy ()
    ledgerEntries := [()]
    completeLedgerInventory := True
    ledgerComplete := trivial
    ledgerCarried := by intro _ _; exact eventCarried () }
  R_S := fun _ => {
    sort := ⟨.P1, by decide⟩
    payload := ()
    moveRecord := ()
    moveRecordCarried := eventCarried ()
    budgetLine := () }
  AdmissibleMove _ z _ _ := z = false

theorem eventRepair : ESystem.RepairStep eventSystem false true () () := by
  exact ⟨eventCarried (), rfl, rfl, rfl, by simp [eventSystem],
    Or.inl ⟨rfl, rfl⟩, rfl, eventCarried ()⟩

def eventEntryClass : RepairEntryClass :=
  ⟨1, .committed_state, true, true⟩

def eventDefectEntry : RepairTypedAuditEntry Unit Unit Unit :=
  .defect () eventEntryClass

def eventMoveEntry : RepairTypedAuditEntry Unit Unit Unit :=
  .move () eventEntryClass

def eventAuditEntry : RepairTypedAuditEntry Unit Unit Unit :=
  .audit () eventEntryClass

def eventHistory : ChallengeHistory Unit Unit Unit Unit Unit Unit Unit Unit where
  episodes := [spikeEpisode]
  repairAuditEntries := [eventDefectEntry, eventMoveEntry, eventAuditEntry]
  entryEpisode _ episode := episode = spikeEpisode
  entryEpisodeDeclared := by
    intro entry h
    exact ⟨spikeEpisode, by simp, rfl⟩
  CompleteChallengeAuditHistory := True

def eventApp (n : Nat) : ClosureApparatus eventSystem where
  time := n
  gateInstrument := eventInstrument
  thresholdRecords := []
  appBoundary := ⟨0⟩
  auditData := ⟨0⟩
  apparatusRecord := ⟨0⟩
  usedLedgerEntries := []
  usedAuditRecords := []

def eventMaintenance : ClosureMaintenanceOperator eventSystem where
  operatorRecord := ⟨0⟩
  apply _ := eventApp 1
  operatorLedgerEntries := [()]
  operatorAuditRecords := [()]

def eventReinstatement : MaintenanceReinstatementRecord eventSystem where
  time := 0
  sourceState := false
  targetState := true
  operatorRecord := eventMaintenance.operatorRecord
  preAppRecord := (eventApp 0).apparatusRecord
  postAppRecord := (eventApp 1).apparatusRecord
  outputRecord := (eventApp 1).apparatusRecord
  reinstatementLedgerEntry := ()

theorem eventAppOccurs (n : Nat) :
    ClosureApparatusOccurrenceFor eventSystem (eventPolicy ⟨0⟩)
      n (eventApp n) := by
  refine ⟨rfl, ?_, eventInstrument.carried, ?_, ?_, ?_⟩
  · exact ⟨1, .committed_state, true, true,
      eventAt (ClosureApparatusRecord.mk 0)⟩
  · intro r h; cases h
  · intro e h; cases h
  · intro a h; cases h

theorem eventMaintenanceOccurs :
    MaintenanceOperatorOccurrenceFor eventSystem (eventPolicy ⟨0⟩)
      0 eventMaintenance := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨1, .committed_state, true, true,
      eventAt (MaintenanceOperatorRecord.mk 0), Or.inl rfl, rfl, rfl⟩
  · intro e h; cases e; simp [eventSystem]
  · intro a h; exact eventCarried ()

theorem eventE3Reinstatement :
    MaintenanceReinstatementFor eventSystem eventHistory
      (eventPolicy ⟨0⟩) (eventPolicy ⟨0⟩)
      (eventPolicy eventReinstatement) 0
      (eventApp 0) (eventApp 1) eventMaintenance eventReinstatement := by
  refine ⟨eventAppOccurs 0, eventAppOccurs 1, eventMaintenanceOccurs, ?_⟩
  refine ⟨1, .committed_state, true, true,
    eventAt eventReinstatement, Or.inl rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, ?_, Or.inl ⟨rfl, rfl⟩⟩
  simp [eventSystem]

theorem eventHistoryAgrees :
    spikeEpisode.time = eventReinstatement.time ∧
      eventTheory.tau spikeEpisode.time = eventReinstatement.sourceState ∧
      eventTheory.tau (spikeEpisode.time + 1) =
        eventReinstatement.targetState ∧
      eventEntryClass.n0 = spikeEpisode.time + 1 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem eventFullyHistoryLinked :
    FullyHistoryLinkedReinstatement eventSystem eventHistory
      (eventPolicy ⟨0⟩) (eventPolicy ⟨0⟩)
      (eventPolicy eventReinstatement) 0
      (eventApp 0) (eventApp 1) eventMaintenance eventReinstatement := by
  refine ⟨eventE3Reinstatement,
    spikeEpisode, (), (), eventEntryClass, ?_⟩
  simp only
  refine ⟨by simp [eventHistory], rfl, rfl,
    by simp [eventHistory, eventDefectEntry],
    by simp [eventHistory, eventMoveEntry, eventEntryClass],
    by simp [eventHistory, eventAuditEntry],
    rfl, rfl, rfl, ?_, ?_, ?_, eventRepair⟩
  · exact eventAt ()
  · exact eventAt ()
  · exact eventAt ()

theorem eventExecutedReinstatement :
    FullyHistoryLinkedReinstatement eventSystem eventHistory
      (eventPolicy ⟨0⟩) (eventPolicy ⟨0⟩)
      (eventPolicy eventReinstatement) 0
      (eventApp 0) (eventApp 1) eventMaintenance eventReinstatement ∧
    eventTheory.tau spikeEpisode.time = false ∧
    eventTheory.tau (spikeEpisode.time + 1) = true ∧
    eventTheory.suppK (eventTheory.tau spikeEpisode.time)
      (eventTheory.tau (spikeEpisode.time + 1)) ∧
    spikeEpisode.time = eventReinstatement.time ∧
    eventEntryClass.n0 = spikeEpisode.time + 1 := by
  exact ⟨eventFullyHistoryLinked, eventTransition.1,
    eventTransition.2.1, eventTransition.2.2,
    eventHistoryAgrees.1, eventHistoryAgrees.2.2.2⟩

#print axioms eventTrajectory
#print axioms eventTransition
#print axioms eventAt
#print axioms eventCarried
#print axioms eventRepair
#print axioms eventAppOccurs
#print axioms eventMaintenanceOccurs
#print axioms eventE3Reinstatement
#print axioms eventHistoryAgrees
#print axioms eventFullyHistoryLinked
#print axioms eventExecutedReinstatement

end SixBirdsFoundationsV.Instances
