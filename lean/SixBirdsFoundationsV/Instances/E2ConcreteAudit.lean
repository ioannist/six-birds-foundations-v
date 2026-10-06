import SixBirdsFoundationsV.Instances.E2TwoLevel

namespace SixBirdsFoundationsV.Instances

def checkedSystemInstrument : ActiveCarriedInstrument spikeTheory (Fin 2)
    Unit Unit Unit Unit Bool (spikePolicy ()) where
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

def checkedSystem : ESystem Unit Unit Unit Unit (Fin 2) Unit Unit Unit Unit Bool where
  T := spikeTheory
  defectRecordPolicy := spikePolicy ()
  moveRecordPolicy := spikePolicy ()
  auditRecordPolicy := spikePolicy true
  I_S := checkedSystemInstrument
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

theorem checkedSystemRepair : ESystem.RepairStep checkedSystem false true () true := by
  exact ⟨spikeCarried (), rfl, rfl, rfl, by simp [checkedSystem],
    rfl, ⟨rfl, rfl⟩, spikeCarried true⟩

def checkedLevelInstrument (i : Fin 2) : ActiveCarriedInstrument spikeTheory
    (Fin 2) Unit Unit Unit Unit Bool (spikePolicy ()) where
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

def checkedLower : CarriedInstrumentLevel checkedSystem where
  levelIndex := 0
  levelTag := 0
  instrument := checkedLevelInstrument 0
  levelRecord := 0
  auditsLowerStack _ := False
  lowerStackTarget := []
  usedLedgerEntries := []
  usedAuditRecords := []

/- Executable check of the lower instrument's visible, carried record. -/
def inspectLower (lower : CarriedInstrumentLevel checkedSystem) : Bool :=
  lower.instrument.visibilityRecords.contains lower.levelRecord

theorem lowerInspectionPasses : inspectLower checkedLower = true := by
  decide

def checkedUpper : CarriedInstrumentLevel checkedSystem where
  levelIndex := 1
  levelTag := 1
  instrument := checkedLevelInstrument 1
  levelRecord := 1
  auditsLowerStack stack := stack = [0] ∧ inspectLower checkedLower = true
  lowerStackTarget := [0]
  usedLedgerEntries := []
  usedAuditRecords := [true]

theorem checkedLowerOccurs :
    CarriedInstrumentLevelOccurrence checkedSystem checkedLower := by
  exact ⟨rfl, (checkedLevelInstrument 0).carried, trivial,
    (by intro e h; cases h), (by intro a h; cases h),
    (by intro k h; cases h)⟩

theorem checkedUpperOccurs :
    CarriedInstrumentLevelOccurrence checkedSystem checkedUpper := by
  exact ⟨rfl, (checkedLevelInstrument 1).carried, trivial,
    (by intro e h; cases h),
    (by intro a h; simp [checkedUpper] at h; subst a; exact spikeCarried true),
    (by intro k h; simp [checkedUpper] at h; subst k; decide)⟩

theorem upperRecordedCheck :
    checkedUpper.usedAuditRecords = [inspectLower checkedLower] ∧
      HasCarriedRecordEvidence checkedSystem.auditRecordPolicy
        (inspectLower checkedLower) ∧
      checkedUpper.auditsLowerStack [0] := by
  refine ⟨?_, ?_, ?_⟩
  · rw [lowerInspectionPasses]
    rfl
  · rw [lowerInspectionPasses]
    exact spikeCarried true
  · exact ⟨rfl, lowerInspectionPasses⟩

def checkedLevel (i : Fin 2) : CarriedInstrumentLevel checkedSystem :=
  if i = 0 then checkedLower else checkedUpper

theorem checkedLevelIndex (i : Fin 2) : (checkedLevel i).levelIndex = i.val := by
  have hv : i.val = 0 ∨ i.val = 1 := by omega
  rcases hv with h | h
  · have hi : i = 0 := Fin.ext h
    subst i; rfl
  · have hi : i = 1 := Fin.ext h
    subst i; rfl

theorem checkedLevelOccurs (i : Fin 2) :
    CarriedInstrumentLevelOccurrence checkedSystem (checkedLevel i) := by
  have hv : i.val = 0 ∨ i.val = 1 := by omega
  rcases hv with h | h
  · have hi : i = 0 := Fin.ext h
    subst i; exact checkedLowerOccurs
  · have hi : i = 1 := Fin.ext h
    subst i; exact checkedUpperOccurs

def checkedMeasure : DeclaredCapacityMeasure checkedSystem where
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
  level := checkedLevel
  levelIndex := checkedLevelIndex
  baseOccurrence := checkedLevelOccurs
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
      simp [checkedLevel, checkedLower, checkedLevelInstrument,
        instrumentId, auditId]
    · have hi : i = 1 := Fin.ext h
      subst i
      simp [checkedLevel, checkedUpper, checkedLevelInstrument,
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

def checkedTower : Nat → Option (CarriedInstrumentLevel checkedSystem) :=
  fun k => if h : k < 2 then some (checkedLevel ⟨k, h⟩) else none

theorem checkedTowerComplete : DeclaredTowerComplete checkedMeasure checkedTower := by
  intro i
  simp [checkedTower, checkedMeasure]

theorem checkedTowerAuditsLowerStack :
    EachLevelAuditsLowerStack checkedSystem checkedTower 2 := by
  intro k level hTower hPositive
  have hlt : k < 2 := hTower.1
  have hk : k = 1 := by omega
  subst k
  have hLevel : level = checkedUpper := by
    have hs := hTower.2.1
    simp [checkedTower, checkedLevel] at hs
    cases hs
    rfl
  subst level
  simpa [checkedUpper] using upperRecordedCheck.2.2

theorem checkedLevelsDisjoint :
    FiniteRecordSet.Disjoint
      (checkedMeasure.records (⟨0, by decide⟩ : Fin checkedMeasure.depth))
      (checkedMeasure.records (⟨1, by decide⟩ : Fin checkedMeasure.depth)) :=
  checkedMeasure.disjointSlots ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide)

theorem checkedRecordListsNodup :
    (declaredRecordList checkedMeasure checkedMeasure.slots).Nodup :=
  declaredRecordList_nodup checkedMeasure checkedMeasure.slots
    checkedMeasure.slotsNodup

theorem checkedConcreteCapacity :
    DeclaredFootprint checkedMeasure = 3 ∧ checkedMeasure.cap true = 3 := by
  decide

theorem checkedCapacityBound :
    DeclaredFootprint checkedMeasure ≤ checkedMeasure.cap true :=
  declaredTowerCapacityBound checkedMeasure checkedTower checkedTowerComplete true

#print axioms checkedSystemRepair
#print axioms lowerInspectionPasses
#print axioms checkedLowerOccurs
#print axioms checkedUpperOccurs
#print axioms upperRecordedCheck
#print axioms checkedLevelIndex
#print axioms checkedLevelOccurs
#print axioms checkedTowerComplete
#print axioms checkedTowerAuditsLowerStack
#print axioms checkedLevelsDisjoint
#print axioms checkedRecordListsNodup
#print axioms checkedConcreteCapacity
#print axioms checkedCapacityBound

end SixBirdsFoundationsV.Instances
