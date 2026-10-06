import SixBirdsFoundationsV.Instances.E6Capped

namespace SixBirdsFoundationsV.Instances

/-- Weighted discharge permits a positive multiplier on an active cap. -/
def weightedCappedObjective (a cap x : Fin 2 → Rat) : Rat :=
  a 0 * min (x 0) (cap 0) + a 1 * min (x 1) (cap 1)

def saturatedSlope (a cap w : Fin 2 → Rat) (p : Fin 2) : Rat :=
  if w p < cap p then a p else 0

/-- At the kink the supporting slope is chosen to be zero. -/
theorem weightedSaturatedSupportingPlane (a cap w x : Fin 2 → Rat)
    (ha : ∀ p, 0 ≤ a p) :
    weightedCappedObjective a cap x ≤
      weightedCappedObjective a cap w +
        saturatedSlope a cap w 0 * (x 0 - w 0) +
        saturatedSlope a cap w 1 * (x 1 - w 1) := by
  have hpart (p : Fin 2) :
      a p * min (x p) (cap p) ≤
        a p * min (w p) (cap p) +
          saturatedSlope a cap w p * (x p - w p) := by
    by_cases h : w p < cap p
    · have hx : min (x p) (cap p) ≤ x p := by grind
      have hm := Rat.mul_le_mul_of_nonneg_left hx (ha p)
      have hw : min (w p) (cap p) = w p := by grind
      have hs : saturatedSlope a cap w p = a p := by simp [saturatedSlope, h]
      have heq : a p * w p + a p * (x p - w p) = a p * x p := by
        grind [Rat.mul_add, Rat.sub_eq_add_neg]
      rw [hw, hs, heq]
      exact hm
    · have hc : min (x p) (cap p) ≤ cap p := by grind
      have hm := Rat.mul_le_mul_of_nonneg_left hc (ha p)
      have hw : min (w p) (cap p) = cap p := by grind
      have hs : saturatedSlope a cap w p = 0 := by simp [saturatedSlope, h]
      rw [hw, hs]
      grind
  have h0 := hpart 0
  have h1 := hpart 1
  unfold weightedCappedObjective
  grind

/-- KKT data for the linear objective on the capped box. The same data certify
the capped objective on the larger nonnegative budget simplex. -/
structure CapMultiplierKKT (a cap : Fin 2 → Rat) (budget : Rat)
    (w : Fin 2 → Rat) where
  feasible : cappedFeasible budget w
  withinCap : ∀ p, w p ≤ cap p
  lambda : Rat
  muAt : Fin 2 → Rat
  lambdaNonnegative : 0 ≤ lambda
  muNonnegative : ∀ p, 0 ≤ muAt p
  stationarity : ∀ p, a p = lambda + muAt p
  capComplementary : ∀ p, muAt p * (cap p - w p) = 0
  budgetComplementary : lambda * (budget - (w 0 + w 1)) = 0

private theorem capDualBound (a cap x : Fin 2 → Rat) (p : Fin 2)
    (lam mu : Rat) (hlam : 0 ≤ lam) (hmu : 0 ≤ mu)
    (ha : a p = lam + mu) :
    a p * min (x p) (cap p) ≤ lam * x p + mu * cap p := by
  have hx : min (x p) (cap p) ≤ x p := by grind
  have hc : min (x p) (cap p) ≤ cap p := by grind
  have hlamx := Rat.mul_le_mul_of_nonneg_left hx hlam
  have hmuc := Rat.mul_le_mul_of_nonneg_left hc hmu
  rw [ha]
  grind [Rat.add_mul]

/-- Global sufficiency includes candidates on either or both caps. -/
theorem capMultiplierKKT_sufficient (a cap : Fin 2 → Rat)
    (budget : Rat) (w x : Fin 2 → Rat)
    (k : CapMultiplierKKT a cap budget w)
    (hx : cappedFeasible budget x) :
    weightedCappedObjective a cap x ≤ weightedCappedObjective a cap w := by
  have h0 := capDualBound a cap x 0 k.lambda (k.muAt 0)
    k.lambdaNonnegative (k.muNonnegative 0) (k.stationarity 0)
  have h1 := capDualBound a cap x 1 k.lambda (k.muAt 1)
    k.lambdaNonnegative (k.muNonnegative 1) (k.stationarity 1)
  rw [k.stationarity 0] at h0
  rw [k.stationarity 1] at h1
  have hw0 : min (w 0) (cap 0) = w 0 := by grind [k.withinCap 0]
  have hw1 : min (w 1) (cap 1) = w 1 := by grind [k.withinCap 1]
  have hc0 := k.capComplementary 0
  have hc1 := k.capComplementary 1
  have hb := k.budgetComplementary
  have hbudget := hx.2.2
  have hlambudget := Rat.mul_le_mul_of_nonneg_left hbudget k.lambdaNonnegative
  unfold weightedCappedObjective
  rw [hw0, hw1]
  rw [k.stationarity 0, k.stationarity 1]
  calc
    (k.lambda + k.muAt 0) * min (x 0) (cap 0) +
        (k.lambda + k.muAt 1) * min (x 1) (cap 1)
        ≤ k.lambda * x 0 + k.muAt 0 * cap 0 +
            (k.lambda * x 1 + k.muAt 1 * cap 1) := by grind
    _ = k.lambda * (x 0 + x 1) +
          (k.muAt 0 * cap 0 + k.muAt 1 * cap 1) := by
          grind [Rat.mul_add]
    _ ≤ k.lambda * budget +
          (k.muAt 0 * cap 0 + k.muAt 1 * cap 1) := by grind
    _ = (k.lambda + k.muAt 0) * w 0 +
          (k.lambda + k.muAt 1) * w 1 := by
          grind [Rat.add_mul, Rat.mul_add, Rat.sub_eq_add_neg]

def capExample : Fin 2 → Rat := fun p => if p = 0 then 1 else 5
def weightExample : Fin 2 → Rat := fun p => if p = 0 then 2 else 1
def optimumAtCap : Fin 2 → Rat := fun p => if p = 0 then 1 else 2
def multiplierAtCap : Fin 2 → Rat := fun p => if p = 0 then 1 else 0

def capExampleKKT :
    CapMultiplierKKT weightExample capExample 3 optimumAtCap := by
  refine ⟨?_, ?_, 1, multiplierAtCap, ?_, ?_, ?_, ?_, ?_⟩
  · grind [cappedFeasible, optimumAtCap]
  · intro p
    have hp : p = 0 ∨ p = 1 := by have := p.isLt; omega
    rcases hp with h | h <;> subst p <;> grind [optimumAtCap, capExample]
  · decide
  · intro p
    have hp : p = 0 ∨ p = 1 := by have := p.isLt; omega
    rcases hp with h | h <;> subst p <;> grind [multiplierAtCap]
  · intro p
    have hp : p = 0 ∨ p = 1 := by have := p.isLt; omega
    rcases hp with h | h <;> subst p <;> grind [weightExample, multiplierAtCap]
  · intro p
    have hp : p = 0 ∨ p = 1 := by have := p.isLt; omega
    rcases hp with h | h <;> subst p <;> grind [multiplierAtCap, capExample, optimumAtCap]
  · grind [optimumAtCap]

theorem capExampleSlopeZero :
    saturatedSlope weightExample capExample optimumAtCap 0 = 0 ∧
    capExampleKKT.muAt 0 = 1 ∧ 0 < capExampleKKT.muAt 0 := by
  constructor
  · grind [saturatedSlope, capExample, optimumAtCap]
  · constructor
    · rfl
    · decide

theorem capExampleGloballyOptimal (x : Fin 2 → Rat)
    (hx : cappedFeasible 3 x) :
    weightedCappedObjective weightExample capExample x ≤
      weightedCappedObjective weightExample capExample optimumAtCap :=
  capMultiplierKKT_sufficient weightExample capExample 3 optimumAtCap x
    capExampleKKT hx

/-- The requested unit-weight instance also attains the budget upper bound. -/
theorem unitCapExampleGloballyOptimal (x : Fin 2 → Rat)
    (hx : cappedFeasible 3 x) :
    cappedObjective capExample x ≤
      cappedObjective capExample optimumAtCap := by
  have h0 : min (x 0) (capExample 0) ≤ x 0 := by grind
  have h1 : min (x 1) (capExample 1) ≤ x 1 := by grind
  have hb := hx.2.2
  grind [cappedObjective, capExample, optimumAtCap]

#print axioms capMultiplierKKT_sufficient
#print axioms weightedSaturatedSupportingPlane
#print axioms capExampleKKT
#print axioms capExampleSlopeZero
#print axioms capExampleGloballyOptimal
#print axioms unitCapExampleGloballyOptimal

end SixBirdsFoundationsV.Instances
