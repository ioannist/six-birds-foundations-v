import SixBirdsFoundationsV.Laws.E6E9PricedAccess

namespace SixBirdsFoundationsV.Instances

/- A two-probe, unit-cost affine discharge problem. -/
def affineObjective (x : Fin 2 → Rat) : Rat := x 0 + x 1

def affineFeasible (x : Fin 2 → Rat) : Prop :=
  0 ≤ x 0 ∧ 0 ≤ x 1 ∧ affineObjective x ≤ 1

def affineKKTAllocation : Fin 2 → Rat := fun p => if p = 0 then 1 else 0

def affineFamily (XiFamily : Type v) : ActiveFamily (Fin 2) XiFamily :=
  { support := [0, 1], weight := affineKKTAllocation, asXiFamily := none }

def affineMarginalDischarge (XiFamily : Type v) :
    MarginalDischarge (Fin 2) XiFamily := fun _ _ => 1

def affineMarginalCost (XiFamily : Type v) :
    MarginalCost (Fin 2) XiFamily := fun _ _ => 1

def E6_affine_KKT
    {FData RuleFamily ResidualFamily AuditAccessData : Type}
    {InstrumentRecord LedgerEntry DefectRecord MovePayload MoveRecord AuditRecord : Type}
    {S : ESystem FData RuleFamily ResidualFamily AuditAccessData
      InstrumentRecord LedgerEntry DefectRecord MovePayload MoveRecord AuditRecord}
    {XiFamily : Type} {economy : ProbeEconomy S (Fin 2) XiFamily}
    {move : ProbeMove (Fin 2) XiFamily}
    (budgetData : ExposureBudgetWitness economy move)
    (hBinding : BindingExposureBudget budgetData) :
    KKTWitness (affineFamily XiFamily) budgetData
      (affineMarginalDischarge XiFamily) (affineMarginalCost XiFamily) := by
  refine ⟨1, fun _ => 0, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · intro p; exact Rat.le_refl
  · rw [hBinding.2]; grind
  · intro p; grind
  · intro p hp; grind [affineMarginalDischarge, affineMarginalCost]

theorem affineKKTAllocation_feasible : affineFeasible affineKKTAllocation := by
  grind [affineFeasible, affineObjective, affineKKTAllocation]

theorem affineKKTAllocation_binding :
    affineObjective affineKKTAllocation = 1 := by
  grind [affineObjective, affineKKTAllocation]

theorem E6_affine_optimal (x : Fin 2 → Rat) (hx : affineFeasible x) :
    affineObjective x ≤ affineObjective affineKKTAllocation := by
  rw [affineKKTAllocation_binding]
  exact hx.2.2

theorem E6_affine_budget_link
    {FData RuleFamily ResidualFamily AuditAccessData : Type}
    {InstrumentRecord LedgerEntry DefectRecord MovePayload MoveRecord AuditRecord : Type}
    {S : ESystem FData RuleFamily ResidualFamily AuditAccessData
      InstrumentRecord LedgerEntry DefectRecord MovePayload MoveRecord AuditRecord}
    {XiFamily : Type} {economy : ProbeEconomy S (Fin 2) XiFamily}
    {move : ProbeMove (Fin 2) XiFamily}
    (budgetData : ExposureBudgetWitness economy move)
    (hBinding : BindingExposureBudget budgetData)
    (hSpend : budgetData.spend = affineObjective affineKKTAllocation) :
    budgetData.budget = affineObjective affineKKTAllocation := by
  rw [← hBinding.2]
  exact hSpend

theorem E6_affine_budget_link_assuming_spend_eq_objective
    {FData RuleFamily ResidualFamily AuditAccessData : Type}
    {InstrumentRecord LedgerEntry DefectRecord MovePayload MoveRecord AuditRecord : Type}
    {S : ESystem FData RuleFamily ResidualFamily AuditAccessData
      InstrumentRecord LedgerEntry DefectRecord MovePayload MoveRecord AuditRecord}
    {XiFamily : Type} {economy : ProbeEconomy S (Fin 2) XiFamily}
    {move : ProbeMove (Fin 2) XiFamily}
    (budgetData : ExposureBudgetWitness economy move)
    (hBinding : BindingExposureBudget budgetData)
    (hSpendEqObjective :
      budgetData.spend = affineObjective affineKKTAllocation) :
    budgetData.budget = affineObjective affineKKTAllocation :=
  E6_affine_budget_link budgetData hBinding hSpendEqObjective

theorem E6_affine_optimal_for_budget
    {FData RuleFamily ResidualFamily AuditAccessData : Type}
    {InstrumentRecord LedgerEntry DefectRecord MovePayload MoveRecord AuditRecord : Type}
    {S : ESystem FData RuleFamily ResidualFamily AuditAccessData
      InstrumentRecord LedgerEntry DefectRecord MovePayload MoveRecord AuditRecord}
    {XiFamily : Type} {economy : ProbeEconomy S (Fin 2) XiFamily}
    {move : ProbeMove (Fin 2) XiFamily}
    (budgetData : ExposureBudgetWitness economy move)
    (hBinding : BindingExposureBudget budgetData)
    (hSpend : budgetData.spend = affineObjective affineKKTAllocation)
    (x : Fin 2 → Rat) (hx : affineObjective x ≤ budgetData.budget) :
    affineObjective x ≤ affineObjective affineKKTAllocation := by
  rw [E6_affine_budget_link budgetData hBinding hSpend] at hx
  exact hx

theorem E6_affine_positive_multiplier
    {FData RuleFamily ResidualFamily AuditAccessData : Type}
    {InstrumentRecord LedgerEntry DefectRecord MovePayload MoveRecord AuditRecord : Type}
    {S : ESystem FData RuleFamily ResidualFamily AuditAccessData
      InstrumentRecord LedgerEntry DefectRecord MovePayload MoveRecord AuditRecord}
    {XiFamily : Type} {economy : ProbeEconomy S (Fin 2) XiFamily}
    {move : ProbeMove (Fin 2) XiFamily}
    (budgetData : ExposureBudgetWitness economy move)
    (hBinding : BindingExposureBudget budgetData) :
    (E6_affine_KKT budgetData hBinding).lambda > 0 := by
  have hCosts : PositiveMarginalCosts
      (affineMarginalCost XiFamily) (affineFamily XiFamily) := by
    grind [PositiveMarginalCosts, affineMarginalCost]
  have hScarcity : GenuineScarcity (affineFamily XiFamily)
      (affineMarginalDischarge XiFamily) := by
    refine ⟨0, ?_, ?_⟩
    · change (0 : Fin 2) ∈ [0, 1] ∧ (0 : Rat) < affineKKTAllocation 0
      constructor
      · decide
      · change (0 : Rat) < 1
        decide
    · grind [affineMarginalDischarge]
  exact (E6_AttentionKKT (E6_affine_KKT budgetData hBinding)
    hCosts hBinding hScarcity).1

#print axioms affineKKTAllocation_feasible
#print axioms affineKKTAllocation_binding
#print axioms E6_affine_KKT
#print axioms E6_affine_optimal
#print axioms E6_affine_budget_link
#print axioms E6_affine_budget_link_assuming_spend_eq_objective
#print axioms E6_affine_optimal_for_budget
#print axioms E6_affine_positive_multiplier

end SixBirdsFoundationsV.Instances
