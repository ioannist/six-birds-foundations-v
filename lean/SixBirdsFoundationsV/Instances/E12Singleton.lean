import SixBirdsFoundationsV.Laws.E12Individuation

namespace SixBirdsFoundationsV.Instances

def singletonCandidates
    {FData : Type u} {RuleFamily : Type v}
    {ResidualFamily : Type w} {AuditAccessData : Type x}
    (T : TheoryPackage FData RuleFamily ResidualFamily AuditAccessData)
    (I : Subcarrier T) : Candidates T :=
  { members := [I], declaredCandidateFamily := True, declared := trivial }

theorem E12_singleton_maximal_from_tests
    {FData : Type u} {RuleFamily : Type v}
    {ResidualFamily : Type w} {AuditAccessData : Type x}
    {InstrumentRecord : Type y} {LedgerEntry : Type y'}
    {DefectRecord : Type y''} {MovePayload : Type y'''}
    {MoveRecord : Type y''''} {AuditRecord : Type y'''''}
    {ChallengeClass : Type z} {SourceQuotient : Type z'}
    {DeclaredFamily : Type z''} {TargetReadout : Type z'''}
    {ObstructionWitness : Type z''''}
    {Probe : Type z'''''} {XiFamily : Type z''''''}
    (S : ESystem FData RuleFamily ResidualFamily AuditAccessData
      InstrumentRecord LedgerEntry DefectRecord MovePayload MoveRecord AuditRecord)
    (H : ChallengeHistory ChallengeClass SourceQuotient DeclaredFamily
      TargetReadout ObstructionWitness DefectRecord MoveRecord AuditRecord)
    (recordPolicyI : CarriedRecordPolicy S.T LedgerEntry)
    (generatedBy : GeneratedByActivityIn S)
    (sourceStatePolicy : CarriedRecordPolicy S.T S.T.Z)
    (accessPolicyRecord : CarriedRecordPolicy S.T (AccessPolicy Probe XiFamily))
    (viabilityProbes : DeclaredViabilityProbes S.T)
    (sufficiency : SufficiencyClosureCertified viabilityProbes)
    (appPolicy : CarriedRecordPolicy S.T ClosureApparatusRecord)
    (maintenancePolicy : CarriedRecordPolicy S.T MaintenanceOperatorRecord)
    (reinstatementPolicy : CarriedRecordPolicy S.T (MaintenanceReinstatementRecord S))
    (boundaryApparatus : BoundaryApparatusFor S)
    (I : Subcarrier S.T)
    (hRepair : RepairClosedOn S sourceStatePolicy I)
    (hBudget : BudgetClosedOn S recordPolicyI accessPolicyRecord I)
    (hRecord : RecordClosedOn S recordPolicyI generatedBy I)
    (B : InstitutionalBoundaryCandidate I)
    (coarsest : CoarsestQuotientCertified viabilityProbes sufficiency
      B.interfaceQuotient)
    (hViable : ViabilitySufficientBoundary viabilityProbes sufficiency B coarsest)
    (hMaintained : SelfMaintainedBoundary S H appPolicy maintenancePolicy
      reinstatementPolicy boundaryApparatus I B) :
    IntegratedCase S H recordPolicyI generatedBy sourceStatePolicy
      accessPolicyRecord viabilityProbes sufficiency appPolicy maintenancePolicy
      reinstatementPolicy boundaryApparatus (singletonCandidates S.T I) I := by
  have hInd : Individuates S H recordPolicyI generatedBy sourceStatePolicy
      accessPolicyRecord viabilityProbes sufficiency appPolicy maintenancePolicy
      reinstatementPolicy boundaryApparatus I :=
    ⟨hRepair, hBudget, hRecord, B, coarsest, hViable, hMaintained⟩
  constructor
  · refine ⟨by simp [singletonCandidates], hInd, ?_⟩
    intro I' hMember _ _
    simpa [singletonCandidates] using hMember
  · intro hOverlap
    rcases hOverlap with ⟨I', hMember, _, hNe, _⟩
    have hEq : I' = I := by simpa [singletonCandidates] using hMember
    exact hNe hEq

#print axioms E12_singleton_maximal_from_tests

end SixBirdsFoundationsV.Instances
