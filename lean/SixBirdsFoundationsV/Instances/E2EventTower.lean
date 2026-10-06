import SixBirdsFoundationsV.Instances.E2Downstream
import SixBirdsFoundationsV.Instances.E3Executed

namespace SixBirdsFoundationsV.Instances

def eventCheckedSystemInstrument : ActiveCarriedInstrument eventTheory (Fin 2)
    Unit Unit Unit Unit Bool (eventPolicy ()) where
  instrument := SixBirdsIII.baseInstrument
  instrumentRecordCarried _ := True
  recordsAreCompleteInventory := True
  visibilityRecords := []
  thresholdRecords := []
  checkRuleRecords := []
  carried := ⟨trivial, trivial, trivial, trivial⟩
  Detects z _ := z = false
  GateAllows z _ _ := z = false
  ReAudits _ _ z' audit := z' = true ∧ audit = true

def eventCheckedSystem : ESystem Unit Unit Unit Unit (Fin 2) Unit Unit Unit Unit Bool where
  T := eventTheory
  defectRecordPolicy := eventPolicy ()
  moveRecordPolicy := eventPolicy ()
  auditRecordPolicy := eventPolicy true
  I_S := eventCheckedSystemInstrument
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

theorem eventCheckedSystemRepair : ESystem.RepairStep eventCheckedSystem false true () true := by
  exact ⟨eventCarried (), rfl, rfl, rfl, by simp [eventCheckedSystem],
    Or.inl ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, eventCarried true⟩

def eventCheckedLevelInstrument (i : Fin 2) : ActiveCarriedInstrument eventTheory
    (Fin 2) Unit Unit Unit Unit Bool (eventPolicy ()) where
  instrument := SixBirdsIII.baseInstrument
  instrumentRecordCarried r := r = i
  recordsAreCompleteInventory := True
  visibilityRecords := [i]
  thresholdRecords := []
  checkRuleRecords := []
  carried := by simp [CarriedInstrument, AllRecords]
  Detects z _ := z = false
  GateAllows z _ _ := z = false
  ReAudits _ _ z' audit := z' = true ∧ audit = true

def eventCheckedLower : CarriedInstrumentLevel eventCheckedSystem where
  levelIndex := 0
  levelTag := 0
  instrument := eventCheckedLevelInstrument 0
  levelRecord := 0
  auditsLowerStack _ := False
  lowerStackTarget := []
  usedLedgerEntries := []
  usedAuditRecords := []

/- Executable check of the lower instrument's visible, carried record. -/
def eventInspectLower (lower : CarriedInstrumentLevel eventCheckedSystem) : Bool :=
  lower.instrument.visibilityRecords.contains lower.levelRecord

theorem eventLowerInspectionPasses : eventInspectLower eventCheckedLower = true := by
  decide

def eventCheckedUpper : CarriedInstrumentLevel eventCheckedSystem where
  levelIndex := 1
  levelTag := 1
  instrument := eventCheckedLevelInstrument 1
  levelRecord := 1
  auditsLowerStack stack := stack = [0] ∧ eventInspectLower eventCheckedLower = true
  lowerStackTarget := [0]
  usedLedgerEntries := []
  usedAuditRecords := [true]

theorem eventCheckedLowerOccurs :
    CarriedInstrumentLevelOccurrence eventCheckedSystem eventCheckedLower := by
  exact ⟨rfl, (eventCheckedLevelInstrument 0).carried, trivial,
    (by intro e h; cases h), (by intro a h; cases h),
    (by intro k h; cases h)⟩

theorem eventCheckedUpperOccurs :
    CarriedInstrumentLevelOccurrence eventCheckedSystem eventCheckedUpper := by
  exact ⟨rfl, (eventCheckedLevelInstrument 1).carried, trivial,
    (by intro e h; cases h),
    (by intro a h; simp [eventCheckedUpper] at h; subst a; exact eventCarried true),
    (by intro k h; simp [eventCheckedUpper] at h; subst k; decide)⟩

theorem eventUpperRecordedCheck :
    eventCheckedUpper.usedAuditRecords = [eventInspectLower eventCheckedLower] ∧
      HasCarriedRecordEvidence eventCheckedSystem.auditRecordPolicy
        (eventInspectLower eventCheckedLower) ∧
      eventCheckedUpper.auditsLowerStack [0] := by
  refine ⟨?_, ?_, ?_⟩
  · rw [eventLowerInspectionPasses]
    rfl
  · rw [eventLowerInspectionPasses]
    exact eventCarried true
  · exact ⟨rfl, eventLowerInspectionPasses⟩

def eventCheckedLevel (i : Fin 2) : CarriedInstrumentLevel eventCheckedSystem :=
  if i = 0 then eventCheckedLower else eventCheckedUpper

theorem eventCheckedLevelIndex (i : Fin 2) : (eventCheckedLevel i).levelIndex = i.val := by
  have hv : i.val = 0 ∨ i.val = 1 := by omega
  rcases hv with h | h
  · have hi : i = 0 := Fin.ext h
    subst i; rfl
  · have hi : i = 1 := Fin.ext h
    subst i; rfl

theorem eventCheckedLevelOccurs (i : Fin 2) :
    CarriedInstrumentLevelOccurrence eventCheckedSystem (eventCheckedLevel i) := by
  have hv : i.val = 0 ∨ i.val = 1 := by omega
  rcases hv with h | h
  · have hi : i = 0 := Fin.ext h
    subst i; exact eventCheckedLowerOccurs
  · have hi : i = 1 := Fin.ext h
    subst i; exact eventCheckedUpperOccurs

def eventCheckedMeasure : DeclaredCapacityMeasure eventCheckedSystem where
  depth := 2
  slots := [0, 1]
  slotsNodup := by decide
  slotsComplete := by
    intro i
    have hv : i.val = 0 ∨ i.val = 1 := by omega
    rcases hv with h | h
    · have hi : i = 0 := Fin.ext h
      subst i; decide
    · have hi : i = 1 := Fin.ext h
      subst i; decide
  level := eventCheckedLevel
  levelIndex := eventCheckedLevelIndex
  baseOccurrence := eventCheckedLevelOccurs
  RecordId := TaggedRecordId (Fin 2) Unit Bool
  instrumentId := instrumentId
  ledgerId := ledgerId
  auditId := auditId
  instrumentInjective := by intro a b h; exact E2_instrument_ids_injective h
  ledgerInjective := by intro a b h; exact E2_ledger_ids_injective h
  auditInjective := by intro a b h; exact E2_audit_ids_injective h
  instrumentLedgerDisjoint := by intro i l; exact E2_instrument_ledger_disjoint i l
  instrumentAuditDisjoint := by intro i a; exact E2_instrument_audit_disjoint i a
  ledgerAuditDisjoint := by intro l a; exact E2_ledger_audit_disjoint l a
  carrierUniverse := fun _ =>
    ⟨[instrumentId 0, instrumentId 1, auditId true],
      by
        apply List.nodup_cons.mpr
        constructor
        · intro h
          rcases List.mem_cons.mp h with hEq | hRest
          · exact (by decide : (0 : Fin 2) ≠ 1)
              (E2_instrument_ids_injective hEq)
          · simp [instrumentId, auditId] at hRest
        · simp [instrumentId, auditId]⟩
  cap := fun _ => 3
  capCard := by intro z; rfl
  records := fun i =>
    if i = 0 then ⟨[instrumentId 0], by simp⟩
    else ⟨[instrumentId 1, auditId true], by simp [instrumentId, auditId]⟩
  countsOnlyCarried := by
    intro i rid
    have hv : i.val = 0 ∨ i.val = 1 := by omega
    rcases hv with h | h
    · have hi : i = 0 := Fin.ext h
      subst i
      simp [eventCheckedLevel, eventCheckedLower, eventCheckedLevelInstrument,
        instrumentId, auditId]
    · have hi : i = 1 := Fin.ext h
      subst i
      simp [eventCheckedLevel, eventCheckedUpper, eventCheckedLevelInstrument,
        instrumentId, auditId]
  withinCarrier := by
    intro z i rid h
    have hv : i.val = 0 ∨ i.val = 1 := by omega
    rcases hv with hi | hi
    · have heq : i = 0 := Fin.ext hi
      subst i
      simp at h ⊢
      exact Or.inl h
    · have heq : i = 1 := Fin.ext hi
      subst i
      simp at h ⊢
      rcases h with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  disjointSlots := by
    intro i j hij rid hi hj
    have hvi : i.val = 0 ∨ i.val = 1 := by omega
    have hvj : j.val = 0 ∨ j.val = 1 := by omega
    rcases hvi with hvi | hvi <;> rcases hvj with hvj | hvj
    · exact hij (Fin.ext (hvi.trans hvj.symm))
    · have hi0 : i = 0 := Fin.ext hvi
      have hj1 : j = 1 := Fin.ext hvj
      subst i; subst j
      simp [instrumentId, auditId] at hi hj
      rcases hj with hj | hj
      · exact (by decide : (0 : Fin 2) ≠ 1)
          (E2_instrument_ids_injective (hi.symm.trans hj))
      · cases hi.symm.trans hj
    · have hi1 : i = 1 := Fin.ext hvi
      have hj0 : j = 0 := Fin.ext hvj
      subst i; subst j
      simp [instrumentId, auditId] at hi hj
      rcases hi with hi | hi
      · exact (by decide : (1 : Fin 2) ≠ 0)
          (E2_instrument_ids_injective (hi.symm.trans hj))
      · cases hi.symm.trans hj
    · exact hij (Fin.ext (hvi.trans hvj.symm))
  positive := by
    intro i
    have hv : i.val = 0 ∨ i.val = 1 := by omega
    rcases hv with h | h
    · have hi : i = 0 := Fin.ext h
      subst i; decide
    · have hi : i = 1 := Fin.ext h
      subst i; decide

def eventCheckedTower : Nat → Option (CarriedInstrumentLevel eventCheckedSystem) :=
  fun k => if h : k < 2 then some (eventCheckedLevel ⟨k, h⟩) else none

theorem eventCheckedTowerComplete : DeclaredTowerComplete eventCheckedMeasure eventCheckedTower := by
  intro i
  simp [eventCheckedTower, eventCheckedMeasure]

theorem eventCheckedTowerAuditsLowerStack :
    EachLevelAuditsLowerStack eventCheckedSystem eventCheckedTower 2 := by
  intro k level hTower hPositive
  have hlt : k < 2 := hTower.1
  have hk : k = 1 := by omega
  subst k
  have hLevel : level = eventCheckedUpper := by
    have hs := hTower.2.1
    simp [eventCheckedTower, eventCheckedLevel] at hs
    cases hs
    rfl
  subst level
  simpa [eventCheckedUpper] using eventUpperRecordedCheck.2.2

theorem eventCheckedLevelsDisjoint :
    FiniteRecordSet.Disjoint
      (eventCheckedMeasure.records (⟨0, by decide⟩ : Fin eventCheckedMeasure.depth))
      (eventCheckedMeasure.records (⟨1, by decide⟩ : Fin eventCheckedMeasure.depth)) :=
  eventCheckedMeasure.disjointSlots ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide)

theorem eventCheckedRecordListsNodup :
    (declaredRecordList eventCheckedMeasure eventCheckedMeasure.slots).Nodup :=
  declaredRecordList_nodup eventCheckedMeasure eventCheckedMeasure.slots
    eventCheckedMeasure.slotsNodup

theorem eventCheckedConcreteCapacity :
    DeclaredFootprint eventCheckedMeasure = 3 ∧ eventCheckedMeasure.cap true = 3 := by
  decide

theorem eventCheckedCapacityBound :
    DeclaredFootprint eventCheckedMeasure ≤ eventCheckedMeasure.cap true :=
  declaredTowerCapacityBound eventCheckedMeasure eventCheckedTower eventCheckedTowerComplete true

#print axioms eventCheckedSystemRepair
#print axioms eventLowerInspectionPasses
#print axioms eventCheckedLowerOccurs
#print axioms eventCheckedUpperOccurs
#print axioms eventUpperRecordedCheck
#print axioms eventCheckedLevelIndex
#print axioms eventCheckedLevelOccurs
#print axioms eventCheckedTowerComplete
#print axioms eventCheckedTowerAuditsLowerStack
#print axioms eventCheckedLevelsDisjoint
#print axioms eventCheckedRecordListsNodup
#print axioms eventCheckedConcreteCapacity
#print axioms eventCheckedCapacityBound

/-- The event-theory tower has exactly its three units of capacity occupied. -/
theorem eventCheckedStatusSaturated :
    DeclaredE2StatusFor eventCheckedMeasure true
      (eventCheckedUpper.auditsLowerStack [0]) False .saturated := by
  exact eventCheckedConcreteCapacity.1.trans eventCheckedConcreteCapacity.2.symm

/-- The repair certified by this tower is the executed false-to-true step. -/
theorem eventCheckedExecutedRepair :
    ESystem.RepairStep eventCheckedSystem
      (eventTheory.tau 0) (eventTheory.tau 1) () true ∧
    eventTheory.tau 0 = false ∧ eventTheory.tau 1 = true ∧
    eventCheckedUpper.usedAuditRecords = [true] := by
  exact ⟨eventCheckedSystemRepair, eventTransition.1, eventTransition.2.1, rfl⟩

#print axioms eventCheckedStatusSaturated
#print axioms eventCheckedExecutedRepair

end SixBirdsFoundationsV.Instances
