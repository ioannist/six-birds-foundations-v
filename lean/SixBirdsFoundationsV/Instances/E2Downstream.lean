import SixBirdsFoundationsV.Instances.E2ConcreteAudit

namespace SixBirdsFoundationsV.Instances

/-- The physical inventory supplies the next level; audit and ordering are
separate facts about that level, rather than consequences of record counting. -/
structure DeclaredFreshBridge {F R E A I L D P M U : Type}
    {S : ESystem F R E A I L D P M U}
    (measure : DeclaredCapacityMeasure S) where
  orderedTags : ∀ i j : Fin measure.depth, i.val < j.val →
    (measure.level i).levelTag < (measure.level j).levelTag
  audits : ∀ j : Fin measure.depth, 0 < j.val →
    (measure.level j).auditsLowerStack (List.range j.val)
  target : ∀ j : Fin measure.depth, 0 < j.val →
    (measure.level j).lowerStackTarget = List.range j.val

theorem declaredForcedStratification {F R E A I L D P M U : Type}
    {S : ESystem F R E A I L D P M U}
    (measure : DeclaredCapacityMeasure S)
    (tower : Nat → Option (CarriedInstrumentLevel S))
    (complete : DeclaredTowerComplete measure tower)
    (bridge : DeclaredFreshBridge measure)
    (n : Nat) (hn : n < measure.depth) :
    ∃ next : CarriedInstrumentLevel S,
      tower n = some next ∧
      CarriedInstrumentLevelOccurrence S next ∧
      next.levelIndex = n ∧
      0 < (measure.records ⟨n, hn⟩).card ∧
      (∀ i : Fin measure.depth, i.val < n →
        (measure.level i).levelTag < next.levelTag) ∧
      (0 < n → next.auditsLowerStack (List.range n) ∧
        next.lowerStackTarget = List.range n) := by
  let slot : Fin measure.depth := ⟨n, hn⟩
  refine ⟨measure.level slot, complete slot, measure.baseOccurrence slot,
    measure.levelIndex slot, measure.positive slot, ?_, ?_⟩
  · intro i hi
    exact bridge.orderedTags i slot hi
  · intro hpos
    exact ⟨bridge.audits slot hpos, bridge.target slot hpos⟩

inductive DeclaredE2Status where
  | saturated
  | rotating
  | circularBlocked
  | activeScoped
  deriving DecidableEq, Repr

/-- A priority classification of the corrected inventory at a state. -/
def DeclaredE2StatusFor {F R E A I L D P M U : Type}
    {S : ESystem F R E A I L D P M U}
    (measure : DeclaredCapacityMeasure S) (z : S.T.Z)
    (auditedUpper selfClaimBlocked : Prop) : DeclaredE2Status → Prop
  | .saturated => DeclaredFootprint measure = measure.cap z
  | .rotating => DeclaredFootprint measure ≠ measure.cap z ∧ auditedUpper
  | .circularBlocked => DeclaredFootprint measure ≠ measure.cap z ∧
      ¬ auditedUpper ∧ selfClaimBlocked
  | .activeScoped => DeclaredFootprint measure ≠ measure.cap z ∧
      ¬ auditedUpper ∧ ¬ selfClaimBlocked

theorem declaredE2StatusPartition {F R E A I L D P M U : Type}
    {S : ESystem F R E A I L D P M U}
    (measure : DeclaredCapacityMeasure S) (z : S.T.Z)
    (auditedUpper selfClaimBlocked : Prop) :
    ∃ status, DeclaredE2StatusFor measure z auditedUpper
      selfClaimBlocked status ∧
      ∀ other, DeclaredE2StatusFor measure z auditedUpper
        selfClaimBlocked other → other = status := by
  classical
  by_cases hsat : DeclaredFootprint measure = measure.cap z
  · refine ⟨.saturated, hsat, ?_⟩
    intro status hs
    cases status with
    | saturated => rfl
    | rotating => exact False.elim (hs.1 hsat)
    | circularBlocked => exact False.elim (hs.1 hsat)
    | activeScoped => exact False.elim (hs.1 hsat)
  · by_cases haudit : auditedUpper
    · refine ⟨.rotating, ⟨hsat, haudit⟩, ?_⟩
      intro status hs
      cases status with
      | saturated => exact False.elim (hsat hs)
      | rotating => rfl
      | circularBlocked => exact False.elim (hs.2.1 haudit)
      | activeScoped => exact False.elim (hs.2.1 haudit)
    · by_cases hblocked : selfClaimBlocked
      · refine ⟨.circularBlocked, ⟨hsat, haudit, hblocked⟩, ?_⟩
        intro status hs
        cases status with
        | saturated => exact False.elim (hsat hs)
        | rotating => exact False.elim (haudit hs.2)
        | circularBlocked => rfl
        | activeScoped => exact False.elim (hs.2.2 hblocked)
      · refine ⟨.activeScoped, ⟨hsat, haudit, hblocked⟩, ?_⟩
        intro status hs
        cases status with
        | saturated => exact False.elim (hsat hs)
        | rotating => exact False.elim (haudit hs.2)
        | circularBlocked => exact False.elim (hblocked hs.2.2)
        | activeScoped => rfl

def checkedFreshBridge : DeclaredFreshBridge checkedMeasure where
  orderedTags := by
    intro i j hij
    have hiBound : i.val < 2 := by simpa [checkedMeasure] using i.isLt
    have hjBound : j.val < 2 := by simpa [checkedMeasure] using j.isLt
    have hiVal : i.val = 0 := by omega
    have hjVal : j.val = 1 := by omega
    have hi : i = ⟨0, by decide⟩ := Fin.ext hiVal
    have hj : j = ⟨1, by decide⟩ := Fin.ext hjVal
    subst i; subst j
    decide
  audits := by
    intro j hj
    have hjBound : j.val < 2 := by simpa [checkedMeasure] using j.isLt
    have hjVal : j.val = 1 := by omega
    have h : j = ⟨1, by decide⟩ := Fin.ext hjVal
    subst j
    exact upperRecordedCheck.2.2
  target := by
    intro j hj
    have hjBound : j.val < 2 := by simpa [checkedMeasure] using j.isLt
    have hjVal : j.val = 1 := by omega
    have h : j = ⟨1, by decide⟩ := Fin.ext hjVal
    subst j
    rfl

theorem checkedForcedStratification :
    ∃ next : CarriedInstrumentLevel checkedSystem,
      checkedTower 1 = some next ∧
      CarriedInstrumentLevelOccurrence checkedSystem next ∧
      next.levelIndex = 1 ∧
      0 < (checkedMeasure.records (⟨1, by decide⟩ : Fin checkedMeasure.depth)).card ∧
      (∀ i : Fin checkedMeasure.depth, i.val < 1 →
        (checkedMeasure.level i).levelTag < next.levelTag) ∧
      next.auditsLowerStack [0] ∧ next.lowerStackTarget = [0] := by
  obtain ⟨next, ht, ho, hi, hp, htags, haudit⟩ :=
  declaredForcedStratification checkedMeasure checkedTower
    checkedTowerComplete checkedFreshBridge 1 (by decide)
  refine ⟨next, ht, ho, hi, hp, htags, ?_⟩
  simpa using haudit (by decide)

theorem checkedStatusSaturated :
    DeclaredE2StatusFor checkedMeasure true
      (checkedUpper.auditsLowerStack [0]) False .saturated := by
  exact checkedConcreteCapacity.1.trans checkedConcreteCapacity.2.symm

theorem checkedStatusPartition :
    ∃ status, DeclaredE2StatusFor checkedMeasure true
      (checkedUpper.auditsLowerStack [0]) False status ∧
      ∀ other, DeclaredE2StatusFor checkedMeasure true
        (checkedUpper.auditsLowerStack [0]) False other → other = status :=
  declaredE2StatusPartition checkedMeasure true _ _

#print axioms declaredForcedStratification
#print axioms declaredE2StatusPartition
#print axioms checkedForcedStratification
#print axioms checkedStatusSaturated
#print axioms checkedStatusPartition

end SixBirdsFoundationsV.Instances
