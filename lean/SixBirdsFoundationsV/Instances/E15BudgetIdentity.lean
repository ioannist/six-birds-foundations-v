import SixBirdsFoundationsV.Laws.E15OfflineReclosure

namespace SixBirdsFoundationsV.Instances

/-- Budget exhaustion and offline gating force the internal reallocation identity. -/
theorem offlineCapacityFromExhaustion
    {ChallengeClass : Type u} (allocation : SharedBudgetAllocationRecord ChallengeClass)
    (budget : Rat)
    (online : allocation.onlineExternalAllocation +
      allocation.onlineInternalDischargeAllocation = budget)
    (offline : allocation.offlineExternalAllocation +
      allocation.offlineInternalDischargeAllocation = budget)
    (gate : allocation.offlineExternalAllocation = 0) :
    allocation.offlineInternalDischargeAllocation =
      allocation.onlineInternalDischargeAllocation +
        allocation.onlineExternalAllocation := by
  calc
    allocation.offlineInternalDischargeAllocation =
        allocation.offlineExternalAllocation +
          allocation.offlineInternalDischargeAllocation := by
            rw [gate]
            exact (Rat.zero_add _).symm
    _ = budget := offline
    _ = allocation.onlineExternalAllocation +
          allocation.onlineInternalDischargeAllocation := online.symm
    _ = allocation.onlineInternalDischargeAllocation +
          allocation.onlineExternalAllocation := Rat.add_comm _ _

theorem geometryCapacityFromExhaustion
    {FData : Type u} {RuleFamily : Type v}
    {ResidualFamily : Type w} {AuditAccessData : Type x}
    {InstrumentRecord : Type y} {LedgerEntry : Type y'}
    {DefectRecord : Type y''} {MovePayload : Type y'''}
    {MoveRecord : Type y''''} {AuditRecord : Type y'''''}
    (S : ESystem FData RuleFamily ResidualFamily AuditAccessData
      InstrumentRecord LedgerEntry DefectRecord MovePayload MoveRecord AuditRecord)
    {X : Type z} {RecordValue : Type z'} {Q : Type z''}
    {TransportedValue : Type z'''} {FOut : Type z''''}
    {Readout : Type z'''''} {RouteResiduePayload : Type z''''''}
    {Probe : Type z'''''''} {XiFamily : Type z''''''''}
    {ChallengeClass : Type z'''''''''} {e yDim xiDim : Nat}
    (policies : OfflineReclosureEvidencePolicies S X RecordValue Q
      TransportedValue FOut Readout RouteResiduePayload ChallengeClass e yDim
      xiDim)
    (scope : ClosureDebtScopeRecord ChallengeClass)
    (economy : ProbeEconomy S Probe XiFamily) (move : ProbeMove Probe XiFamily)
    (budgetData : ExposureBudgetWitness economy move)
    (allocation : SharedBudgetAllocationRecord ChallengeClass)
    (geometry : DerivedOfflineBudgetGeometry S policies scope economy move
      budgetData allocation) :
    kappaOff S geometry = kappaOn S geometry + freedAllocation S geometry := by
  exact offlineCapacityFromExhaustion allocation budgetData.budget
    geometry.onlineExhaustsSharedBudget
    geometry.offlineExhaustsSharedBudget
    geometry.offlineExchangeGated

#print axioms offlineCapacityFromExhaustion
#print axioms geometryCapacityFromExhaustion

end SixBirdsFoundationsV.Instances
