import SixBirdsFoundationsV.Instances.SpikeModel

namespace SixBirdsFoundationsV.Instances

def EpisodeLinkedReinstatement
    {F R E A I L D P M U C Q Fm O W : Type}
    (S : ESystem F R E A I L D P M U)
    (H : ChallengeHistory C Q Fm O W D M U)
    (appPolicy : CarriedRecordPolicy S.T ClosureApparatusRecord)
    (maintenancePolicy : CarriedRecordPolicy S.T MaintenanceOperatorRecord)
    (reinstatementPolicy : CarriedRecordPolicy S.T (MaintenanceReinstatementRecord S))
    (t : Nat) (pre post : ClosureApparatus S)
    (operator : ClosureMaintenanceOperator S)
    (record : MaintenanceReinstatementRecord S) : Prop :=
  MaintenanceReinstatementFor S H appPolicy maintenancePolicy
    reinstatementPolicy t pre post operator record ∧
  ∃ episode : ChallengeEpisode C Q Fm O W,
    ∃ entry : RepairTypedAuditEntry D M U,
      episode ∈ H.episodes ∧
      entry ∈ H.repairAuditEntries ∧
      H.entryEpisode entry episode ∧
      episode.time = t ∧
      RepairTypedAuditEntryCarried S entry ∧
      ∃ defect : D, ∃ audit : U,
        entry = .move (S.R_S defect).moveRecord entry.entryClass ∧
        ESystem.RepairStep S record.sourceState record.targetState defect audit

def spikeEpisode : ChallengeEpisode Unit Unit Unit Unit Unit where
  time := 0
  challengeClass := ()
  sourceQuotient := ()
  declaredFamily := ()
  targetReadout := ()
  obstructionWitness := some ()

def spikeEntry : RepairTypedAuditEntry Unit Unit Unit :=
  .move () ⟨0, .committed_state, true, true⟩

def spikeHistory : ChallengeHistory Unit Unit Unit Unit Unit Unit Unit Unit where
  episodes := [spikeEpisode]
  repairAuditEntries := [spikeEntry]
  entryEpisode entry episode := entry = spikeEntry ∧ episode = spikeEpisode
  entryEpisodeDeclared := by
    intro entry h
    have he : entry = spikeEntry := by simpa [spikeEntry] using h
    subst entry
    exact ⟨spikeEpisode, by simp, rfl, rfl⟩
  CompleteChallengeAuditHistory := True

theorem spikeEpisodeLinked :
    EpisodeLinkedReinstatement spikeSystem spikeHistory
      (spikePolicy ⟨0⟩) (spikePolicy ⟨0⟩)
      (spikePolicy spikeReinstatement) 0 (spikeApp 0) (spikeApp 1)
      spikeMaintenance spikeReinstatement := by
  refine ⟨spikeE3Reinstatement spikeHistory,
    spikeEpisode, spikeEntry, by simp [spikeHistory],
    by simp [spikeHistory], ?_, rfl, ?_, (), (), ?_, spikeRepair⟩
  · exact ⟨rfl, rfl⟩
  · exact spikeAt ()
  · rfl

theorem noEpisodeLinkedWithEmptyHistory
    {F R E A I L D P M U C Q Fm O W : Type}
    (S : ESystem F R E A I L D P M U)
    (H : ChallengeHistory C Q Fm O W D M U)
    (hEmpty : H.episodes = [])
    (appPolicy : CarriedRecordPolicy S.T ClosureApparatusRecord)
    (maintenancePolicy : CarriedRecordPolicy S.T MaintenanceOperatorRecord)
    (reinstatementPolicy : CarriedRecordPolicy S.T (MaintenanceReinstatementRecord S))
    (t : Nat) (pre post : ClosureApparatus S)
    (operator : ClosureMaintenanceOperator S)
    (record : MaintenanceReinstatementRecord S) :
    ¬ EpisodeLinkedReinstatement S H appPolicy maintenancePolicy
      reinstatementPolicy t pre post operator record := by
  intro h
  rcases h.2 with ⟨episode, entry, hEpisode, _⟩
  simp [hEmpty] at hEpisode

def FullyHistoryLinkedReinstatement
    {F R E A I L D P M U C Q Fm O : Type}
    (S : ESystem F R E A I L D P M U)
    (H : ChallengeHistory C Q Fm O D D M U)
    (appPolicy : CarriedRecordPolicy S.T ClosureApparatusRecord)
    (maintenancePolicy : CarriedRecordPolicy S.T MaintenanceOperatorRecord)
    (reinstatementPolicy : CarriedRecordPolicy S.T (MaintenanceReinstatementRecord S))
    (t : Nat) (pre post : ClosureApparatus S)
    (operator : ClosureMaintenanceOperator S)
    (record : MaintenanceReinstatementRecord S) : Prop :=
  MaintenanceReinstatementFor S H appPolicy maintenancePolicy
    reinstatementPolicy t pre post operator record ∧
  ∃ episode : ChallengeEpisode C Q Fm O D,
    ∃ defect : D, ∃ audit : U, ∃ entryClass : RepairEntryClass,
      let defectEntry : RepairTypedAuditEntry D M U := .defect defect entryClass
      let moveEntry : RepairTypedAuditEntry D M U :=
        .move (S.R_S defect).moveRecord entryClass
      let auditEntry : RepairTypedAuditEntry D M U := .audit audit entryClass
      episode ∈ H.episodes ∧
      episode.time = t ∧
      episode.obstructionWitness = some defect ∧
      defectEntry ∈ H.repairAuditEntries ∧
      moveEntry ∈ H.repairAuditEntries ∧
      auditEntry ∈ H.repairAuditEntries ∧
      H.entryEpisode defectEntry episode ∧
      H.entryEpisode moveEntry episode ∧
      H.entryEpisode auditEntry episode ∧
      RepairTypedAuditEntryCarried S defectEntry ∧
      RepairTypedAuditEntryCarried S moveEntry ∧
      RepairTypedAuditEntryCarried S auditEntry ∧
      ESystem.RepairStep S record.sourceState record.targetState defect audit

def spikeEntryClass : RepairEntryClass :=
  ⟨0, .committed_state, true, true⟩

def spikeDefectEntry : RepairTypedAuditEntry Unit Unit Unit :=
  .defect () spikeEntryClass

def spikeAuditEntry : RepairTypedAuditEntry Unit Unit Unit :=
  .audit () spikeEntryClass

def spikeFullHistory : ChallengeHistory Unit Unit Unit Unit Unit Unit Unit Unit where
  episodes := [spikeEpisode]
  repairAuditEntries := [spikeDefectEntry, spikeEntry, spikeAuditEntry]
  entryEpisode _ episode := episode = spikeEpisode
  entryEpisodeDeclared := by
    intro entry h
    exact ⟨spikeEpisode, by simp, rfl⟩
  CompleteChallengeAuditHistory := True

theorem spikeFullyHistoryLinked :
    FullyHistoryLinkedReinstatement spikeSystem spikeFullHistory
      (spikePolicy ⟨0⟩) (spikePolicy ⟨0⟩)
      (spikePolicy spikeReinstatement) 0 (spikeApp 0) (spikeApp 1)
      spikeMaintenance spikeReinstatement := by
  refine ⟨spikeE3Reinstatement spikeFullHistory,
    spikeEpisode, (), (), spikeEntryClass, ?_⟩
  simp only
  refine ⟨by simp [spikeFullHistory], rfl, rfl,
    by simp [spikeFullHistory, spikeDefectEntry],
    by simp [spikeFullHistory, spikeEntry, spikeEntryClass],
    by simp [spikeFullHistory, spikeAuditEntry],
    rfl, rfl, rfl, ?_, ?_, ?_, spikeRepair⟩
  · exact spikeAt ()
  · exact spikeAt ()
  · exact spikeAt ()

#print axioms spikeEpisodeLinked
#print axioms noEpisodeLinkedWithEmptyHistory
#print axioms spikeFullyHistoryLinked

end SixBirdsFoundationsV.Instances
