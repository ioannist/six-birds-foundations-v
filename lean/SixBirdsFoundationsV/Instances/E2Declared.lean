import SixBirdsFoundationsV.Instances.SpikeModel
import SixBirdsFoundationsV.Instances.E2TaggedIds

namespace SixBirdsFoundationsV.Instances

structure DeclaredCapacityMeasure
    {F R E A I L D P M U : Type}
    (S : ESystem F R E A I L D P M U) where
  depth : Nat
  slots : List (Fin depth)
  slotsNodup : slots.Nodup
  slotsComplete : ∀ slot : Fin depth, slot ∈ slots
  level : Fin depth → CarriedInstrumentLevel S
  levelIndex : ∀ slot, (level slot).levelIndex = slot.val
  baseOccurrence : ∀ slot, CarriedInstrumentLevelOccurrence S (level slot)
  RecordId : Type
  instrumentId : I → RecordId
  ledgerId : L → RecordId
  auditId : U → RecordId
  instrumentInjective : Function.Injective instrumentId
  ledgerInjective : Function.Injective ledgerId
  auditInjective : Function.Injective auditId
  instrumentLedgerDisjoint : ∀ i l, instrumentId i ≠ ledgerId l
  instrumentAuditDisjoint : ∀ i a, instrumentId i ≠ auditId a
  ledgerAuditDisjoint : ∀ l a, ledgerId l ≠ auditId a
  carrierUniverse : S.T.Z → FiniteRecordSet RecordId
  cap : S.T.Z → Nat
  capCard : ∀ z, (carrierUniverse z).card = cap z
  records : Fin depth → FiniteRecordSet RecordId
  countsOnlyCarried : ∀ slot rid,
    rid ∈ (records slot).records ↔
      rid = instrumentId (level slot).levelRecord ∨
      (∃ r, r ∈ (level slot).instrument.visibilityRecords ∧ rid = instrumentId r) ∨
      (∃ r, r ∈ (level slot).instrument.thresholdRecords ∧ rid = instrumentId r) ∨
      (∃ r, r ∈ (level slot).instrument.checkRuleRecords ∧
        rid = instrumentId r.record) ∨
      (∃ e, e ∈ (level slot).usedLedgerEntries ∧ rid = ledgerId e) ∨
      (∃ a, a ∈ (level slot).usedAuditRecords ∧ rid = auditId a)
  withinCarrier : ∀ z slot, FiniteRecordSet.Subset (records slot) (carrierUniverse z)
  disjointSlots : ∀ i j, i ≠ j → FiniteRecordSet.Disjoint (records i) (records j)
  positive : ∀ slot, 0 < (records slot).card

def DeclaredOccurrence {F R E A I L D P M U : Type}
    {S : ESystem F R E A I L D P M U}
    (measure : DeclaredCapacityMeasure S) (level : CarriedInstrumentLevel S) : Prop :=
  ∃ slot, measure.level slot = level

def DeclaredTowerComplete {F R E A I L D P M U : Type}
    {S : ESystem F R E A I L D P M U}
    (measure : DeclaredCapacityMeasure S)
    (tower : Nat → Option (CarriedInstrumentLevel S)) : Prop :=
  ∀ slot : Fin measure.depth, tower slot.val = some (measure.level slot)

def DeclaredFootprint {F R E A I L D P M U : Type}
    {S : ESystem F R E A I L D P M U}
    (measure : DeclaredCapacityMeasure S) : Nat :=
  measure.slots.foldl
    (fun total slot => total + (measure.records slot).card) 0

def declaredRecordList {F R E A I L D P M U : Type}
    {S : ESystem F R E A I L D P M U}
    (measure : DeclaredCapacityMeasure S) (slots : List (Fin measure.depth)) :
    List measure.RecordId :=
  slots.flatMap (fun slot => (measure.records slot).records)

def declaredSum {α : Type} (f : α → Nat) : List α → Nat
  | [] => 0
  | x :: xs => f x + declaredSum f xs

theorem declaredSum_foldl {α : Type} (f : α → Nat) (xs : List α) :
    xs.foldl (fun total x => total + f x) 0 = declaredSum f xs := by
  have h : ∀ ys : List α, ∀ init : Nat,
      ys.foldl (fun total x => total + f x) init = init + declaredSum f ys := by
    intro ys
    induction ys with
    | nil => intro init; rfl
    | cons x rest ih =>
        intro init
        rw [List.foldl_cons, ih]
        simp [declaredSum]
        omega
  simpa using h xs 0

theorem declaredRecordList_nodup {F R E A I L D P M U : Type}
    {S : ESystem F R E A I L D P M U}
    (measure : DeclaredCapacityMeasure S)
    (slots : List (Fin measure.depth)) (hn : slots.Nodup) :
    (declaredRecordList measure slots).Nodup := by
  induction slots with
  | nil => simp [declaredRecordList]
  | cons i rest ih =>
      have hi : i ∉ rest := (List.nodup_cons.mp hn).1
      have hr : rest.Nodup := (List.nodup_cons.mp hn).2
      change ((measure.records i).records ++ declaredRecordList measure rest).Nodup
      apply List.nodup_append.mpr
      refine ⟨(measure.records i).nodup, ih hr, ?_⟩
      intro left hl right hright heq
      have hm : ∃ j, j ∈ rest ∧ right ∈ (measure.records j).records := by
        simpa [declaredRecordList, List.mem_flatMap] using hright
      rcases hm with ⟨j, hj, hrec⟩
      have hij : i ≠ j := by intro h; exact hi (h ▸ hj)
      exact measure.disjointSlots i j hij left hl (heq ▸ hrec)

theorem declaredRecordList_subset {F R E A I L D P M U : Type}
    {S : ESystem F R E A I L D P M U}
    (measure : DeclaredCapacityMeasure S) (z : S.T.Z)
    (slots : List (Fin measure.depth)) :
    ∀ rid, rid ∈ declaredRecordList measure slots →
      rid ∈ (measure.carrierUniverse z).records := by
  intro rid h
  have hm : ∃ i, i ∈ slots ∧ rid ∈ (measure.records i).records := by
    simpa [declaredRecordList, List.mem_flatMap] using h
  rcases hm with ⟨i, _, hi⟩
  exact measure.withinCarrier z i rid hi

theorem declaredRecordList_length {F R E A I L D P M U : Type}
    {S : ESystem F R E A I L D P M U}
    (measure : DeclaredCapacityMeasure S)
    (slots : List (Fin measure.depth)) :
    (declaredRecordList measure slots).length =
      declaredSum (fun i => (measure.records i).card) slots := by
  induction slots with
  | nil => rfl
  | cons i rest ih =>
      change ((measure.records i).records ++ declaredRecordList measure rest).length =
        (measure.records i).card +
          declaredSum (fun j => (measure.records j).card) rest
      rw [List.length_append, ih]
      rfl

theorem declaredCapacityBound {F R E A I L D P M U : Type}
    {S : ESystem F R E A I L D P M U}
    (measure : DeclaredCapacityMeasure S) (z : S.T.Z) :
    DeclaredFootprint measure ≤ measure.cap z := by
  have hn := declaredRecordList_nodup measure
    measure.slots measure.slotsNodup
  have hs := declaredRecordList_subset measure z measure.slots
  have hlen := list_length_le_of_nodup_subset
    (declaredRecordList measure measure.slots)
    (measure.carrierUniverse z).records hn (measure.carrierUniverse z).nodup hs
  rw [declaredRecordList_length] at hlen
  have hsum := declaredSum_foldl
    (fun i => (measure.records i).card) measure.slots
  unfold DeclaredFootprint
  rw [hsum]
  exact (measure.capCard z) ▸ hlen

theorem declaredTowerCapacityBound {F R E A I L D P M U : Type}
    {S : ESystem F R E A I L D P M U}
    (measure : DeclaredCapacityMeasure S)
    (tower : Nat → Option (CarriedInstrumentLevel S))
    (_complete : DeclaredTowerComplete measure tower)
    (z : S.T.Z) :
    DeclaredFootprint measure ≤ measure.cap z :=
  declaredCapacityBound measure z

theorem reindexNotDeclared {F R E A I L D P M U : Type}
    {S : ESystem F R E A I L D P M U}
    (measure : DeclaredCapacityMeasure S)
    (level : CarriedInstrumentLevel S)
    (hIndex : measure.depth ≤ level.levelIndex) :
    ¬ DeclaredOccurrence measure level := by
  rintro ⟨slot, h⟩
  have heq := congrArg CarriedInstrumentLevel.levelIndex h
  rw [measure.levelIndex slot] at heq
  omega

theorem copiedRecordReindexNotDeclared {F R E A I L D P M U : Type}
    {S : ESystem F R E A I L D P M U}
    (measure : DeclaredCapacityMeasure S)
    (slot : Fin measure.depth) (other : CarriedInstrumentLevel S)
    (hDifferent : other.levelIndex ≠ slot.val)
    (hSameRecord : other.levelRecord = (measure.level slot).levelRecord) :
    ¬ DeclaredOccurrence measure other := by
  rintro ⟨otherSlot, hDeclared⟩
  have hSlotNe : slot ≠ otherSlot := by
    intro h
    subst otherSlot
    have hIndex := congrArg CarriedInstrumentLevel.levelIndex hDeclared
    rw [measure.levelIndex slot] at hIndex
    exact hDifferent hIndex.symm
  let rid := measure.instrumentId (measure.level slot).levelRecord
  have hLeft : rid ∈ (measure.records slot).records :=
    (measure.countsOnlyCarried slot rid).mpr (Or.inl rfl)
  have hRight : rid ∈ (measure.records otherSlot).records := by
    apply (measure.countsOnlyCarried otherSlot rid).mpr
    left
    rw [hDeclared, hSameRecord]
  exact measure.disjointSlots slot otherSlot hSlotNe rid hLeft hRight

def spikeDeclaredMeasure : DeclaredCapacityMeasure spikeSystem where
  depth := 1
  slots := [0]
  slotsNodup := by decide
  slotsComplete := by
    intro slot
    have h : slot = 0 := Subsingleton.elim slot 0
    subst slot
    decide
  level := fun _ => spikeLevel 0
  levelIndex := by
    intro slot
    have h : slot = 0 := Subsingleton.elim slot 0
    subst slot
    rfl
  baseOccurrence := fun _ => spikeLevelOccurs 0
  RecordId := TaggedRecordId Unit Unit Unit
  instrumentId := instrumentId
  ledgerId := ledgerId
  auditId := auditId
  instrumentInjective := by intro a b h; exact E2_instrument_ids_injective h
  ledgerInjective := by intro a b h; exact E2_ledger_ids_injective h
  auditInjective := by intro a b h; exact E2_audit_ids_injective h
  instrumentLedgerDisjoint := by intro i l; exact E2_instrument_ledger_disjoint i l
  instrumentAuditDisjoint := by intro i a; exact E2_instrument_audit_disjoint i a
  ledgerAuditDisjoint := by intro l a; exact E2_ledger_audit_disjoint l a
  carrierUniverse := fun _ => ⟨[.inl ()], by simp⟩
  cap := fun _ => 1
  capCard := by intro z; rfl
  records := fun _ => ⟨[.inl ()], by simp⟩
  countsOnlyCarried := by
    intro slot rid
    simp [spikeLevel, spikeInstrument, instrumentId]
  withinCarrier := by intro z slot rid h; exact h
  disjointSlots := by
    intro i j h
    have hi : i = 0 := Subsingleton.elim i 0
    have hj : j = 0 := Subsingleton.elim j 0
    exact False.elim (h (hi.trans hj.symm))
  positive := by intro slot; decide

theorem spikeDeclaredCapacityBound :
    DeclaredFootprint spikeDeclaredMeasure ≤ spikeDeclaredMeasure.cap true :=
  declaredCapacityBound spikeDeclaredMeasure true

def spikeDeclaredTower : Nat → Option (CarriedInstrumentLevel spikeSystem) :=
  fun k => if k = 0 then some (spikeLevel 0) else none

theorem spikeDeclaredTowerComplete :
    DeclaredTowerComplete spikeDeclaredMeasure spikeDeclaredTower := by
  change ∀ slot : Fin 1,
    spikeDeclaredTower slot.val = some (spikeLevel 0)
  intro slot
  have h : slot = 0 := Subsingleton.elim slot 0
  subst slot
  rfl

theorem spikeTowerCapacityBound :
    DeclaredFootprint spikeDeclaredMeasure ≤ spikeDeclaredMeasure.cap true :=
  declaredTowerCapacityBound spikeDeclaredMeasure spikeDeclaredTower
    spikeDeclaredTowerComplete true

theorem spikeDeclaredNonzero : 0 < DeclaredFootprint spikeDeclaredMeasure := by
  decide

theorem spikeConcreteCapacity :
    DeclaredFootprint spikeDeclaredMeasure = 1 ∧
      spikeDeclaredMeasure.cap true = 1 := by
  decide

theorem spikeReindexedNotDeclared :
    ¬ DeclaredOccurrence spikeDeclaredMeasure (spikeLevel 1) :=
  reindexNotDeclared spikeDeclaredMeasure (spikeLevel 1) (by decide)

#print axioms declaredRecordList_nodup
#print axioms declaredSum_foldl
#print axioms declaredRecordList_subset
#print axioms declaredRecordList_length
#print axioms declaredCapacityBound
#print axioms declaredTowerCapacityBound
#print axioms reindexNotDeclared
#print axioms copiedRecordReindexNotDeclared
#print axioms spikeDeclaredCapacityBound
#print axioms spikeDeclaredTowerComplete
#print axioms spikeTowerCapacityBound
#print axioms spikeDeclaredNonzero
#print axioms spikeConcreteCapacity
#print axioms spikeReindexedNotDeclared

end SixBirdsFoundationsV.Instances
