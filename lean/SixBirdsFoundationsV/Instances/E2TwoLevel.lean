import SixBirdsFoundationsV.Instances.E2Declared

namespace SixBirdsFoundationsV.Instances

/- The Boolean repair device, now with two physical instrument records. -/
def twoLevelSystemInstrument : ActiveCarriedInstrument spikeTheory (Fin 2)
    Unit Unit Unit Unit Unit (spikePolicy ()) where
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

def twoLevelSystem : ESystem Unit Unit Unit Unit (Fin 2) Unit Unit Unit Unit Unit where
  T := spikeTheory
  defectRecordPolicy := spikePolicy ()
  moveRecordPolicy := spikePolicy ()
  auditRecordPolicy := spikePolicy ()
  I_S := twoLevelSystemInstrument
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

theorem twoLevelRepair : ESystem.RepairStep twoLevelSystem false true () () := by
  exact ⟨spikeCarried (), rfl, rfl, rfl, by simp [twoLevelSystem],
    rfl, rfl, spikeCarried ()⟩

def ownLevelInstrument (i : Fin 2) : ActiveCarriedInstrument spikeTheory
    (Fin 2) Unit Unit Unit Unit Unit (spikePolicy ()) where
  instrument := SixBirdsIII.baseInstrument
  instrumentRecordCarried r := r = i
  recordsAreCompleteInventory := True
  visibilityRecords := [i]
  thresholdRecords := []
  checkRuleRecords := []
  carried := by simp [CarriedInstrument, AllRecords]
  Detects z _ := z = false
  GateAllows z _ _ := z = false
  ReAudits _ _ z' _ := z' = true

def twoLevel (i : Fin 2) : CarriedInstrumentLevel twoLevelSystem where
  levelIndex := i.val
  levelTag := i.val
  instrument := ownLevelInstrument i
  levelRecord := i
  auditsLowerStack := fun stack => stack = (if i = 0 then [] else [0])
  lowerStackTarget := if i = 0 then [] else [0]
  usedLedgerEntries := []
  usedAuditRecords := []

theorem twoLevelOccurs (i : Fin 2) :
    CarriedInstrumentLevelOccurrence twoLevelSystem (twoLevel i) := by
  have hi : i = 0 ∨ i = 1 := by
    have hv : i.val = 0 ∨ i.val = 1 := by omega
    rcases hv with h | h
    · left; exact Fin.ext h
    · right; exact Fin.ext h
  rcases hi with rfl | rfl
  · exact ⟨rfl, (ownLevelInstrument 0).carried, trivial,
      (by intro e h; cases h), (by intro a h; cases h),
      (by intro k h; simp [twoLevel] at h)⟩
  · exact ⟨rfl, (ownLevelInstrument 1).carried, trivial,
      (by intro e h; cases h), (by intro a h; cases h),
      (by intro k h; simp [twoLevel] at h; subst k; decide)⟩

def twoLevelMeasure : DeclaredCapacityMeasure twoLevelSystem where
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
  level := twoLevel
  levelIndex := by intro i; rfl
  baseOccurrence := twoLevelOccurs
  RecordId := TaggedRecordId (Fin 2) Unit Unit
  instrumentId := instrumentId
  ledgerId := ledgerId
  auditId := auditId
  instrumentInjective := by intro a b h; exact E2_instrument_ids_injective h
  ledgerInjective := by intro a b h; exact E2_ledger_ids_injective h
  auditInjective := by intro a b h; exact E2_audit_ids_injective h
  instrumentLedgerDisjoint := by intro i l; exact E2_instrument_ledger_disjoint i l
  instrumentAuditDisjoint := by intro i a; exact E2_instrument_audit_disjoint i a
  ledgerAuditDisjoint := by intro l a; exact E2_ledger_audit_disjoint l a
  carrierUniverse := fun _ => ⟨[instrumentId 0, instrumentId 1],
    by
      apply List.nodup_cons.mpr
      constructor
      · intro h
        have heq :
            instrumentId (L := Unit) (A := Unit) (0 : Fin 2) =
              instrumentId (L := Unit) (A := Unit) (1 : Fin 2) := by
          simpa using h
        exact (by decide : (0 : Fin 2) ≠ 1)
          (E2_instrument_ids_injective heq)
      · simp⟩
  cap := fun _ => 2
  capCard := by intro z; rfl
  records := fun i => ⟨[instrumentId i], by simp⟩
  countsOnlyCarried := by
    intro i rid
    simp [twoLevel, ownLevelInstrument, instrumentId]
  withinCarrier := by
    intro z i rid h
    have hv : i.val = 0 ∨ i.val = 1 := by omega
    rcases hv with hi | hi
    · have heq : i = 0 := Fin.ext hi
      subst i
      have h0 : rid = instrumentId (L := Unit) (A := Unit) (0 : Fin 2) := by
        simpa using h
      simp [h0]
    · have heq : i = 1 := Fin.ext hi
      subst i
      have h1 : rid = instrumentId (L := Unit) (A := Unit) (1 : Fin 2) := by
        simpa using h
      simp [h1]
  disjointSlots := by
    intro i j hij rid hi hj
    have hi' : rid = instrumentId i := by simpa using hi
    have hj' : rid = instrumentId j := by simpa using hj
    exact hij (E2_instrument_ids_injective (hi'.symm.trans hj'))
  positive := by intro i; change 0 < 1; decide

def twoLevelTower : Nat → Option (CarriedInstrumentLevel twoLevelSystem) :=
  fun k => if h : k < 2 then some (twoLevel ⟨k, h⟩) else none

theorem twoLevelTowerComplete :
    DeclaredTowerComplete twoLevelMeasure twoLevelTower := by
  intro i
  simp [twoLevelTower, twoLevelMeasure]

theorem twoLevelAuditsFirst :
    (twoLevel (1 : Fin 2)).auditsLowerStack [0] ∧
      (twoLevel (1 : Fin 2)).lowerStackTarget = [0] := by
  simp [twoLevel]

theorem twoLevelAuditsLowerStack :
    EachLevelAuditsLowerStack twoLevelSystem twoLevelTower 2 := by
  intro k level hTower hPositive
  have hlt : k < 2 := hTower.1
  have hk : k = 1 := by omega
  subst k
  have hLevel : level = twoLevel (1 : Fin 2) := by
    have hs := hTower.2.1
    simp [twoLevelTower] at hs
    cases hs
    rfl
  subst level
  simpa using twoLevelAuditsFirst

theorem twoLevelDisjoint :
    FiniteRecordSet.Disjoint
      (twoLevelMeasure.records (⟨0, by decide⟩ : Fin twoLevelMeasure.depth))
      (twoLevelMeasure.records (⟨1, by decide⟩ : Fin twoLevelMeasure.depth)) :=
  twoLevelMeasure.disjointSlots ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide)

theorem twoLevelCountedRecordsNodup :
    (declaredRecordList twoLevelMeasure twoLevelMeasure.slots).Nodup :=
  declaredRecordList_nodup twoLevelMeasure twoLevelMeasure.slots
    twoLevelMeasure.slotsNodup

theorem twoLevelConcreteCapacity :
    DeclaredFootprint twoLevelMeasure = 2 ∧
      twoLevelMeasure.cap true = 2 := by
  decide

theorem twoLevelCapacityBound :
    DeclaredFootprint twoLevelMeasure ≤ twoLevelMeasure.cap true :=
  declaredTowerCapacityBound twoLevelMeasure twoLevelTower
    twoLevelTowerComplete true

#print axioms twoLevelRepair
#print axioms twoLevelOccurs
#print axioms twoLevelTowerComplete
#print axioms twoLevelAuditsFirst
#print axioms twoLevelAuditsLowerStack
#print axioms twoLevelDisjoint
#print axioms twoLevelCountedRecordsNodup
#print axioms twoLevelConcreteCapacity
#print axioms twoLevelCapacityBound

end SixBirdsFoundationsV.Instances
