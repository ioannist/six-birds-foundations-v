import SixBirdsFoundationsV.Instances.E6Affine

namespace SixBirdsFoundationsV.Instances

/-- A two-probe separable piecewise-linear concave discharge objective. -/
def cappedObjective (cap x : Fin 2 → Rat) : Rat :=
  min (x 0) (cap 0) + min (x 1) (cap 1)

def cappedFeasible (budget : Rat) (x : Fin 2 → Rat) : Prop :=
  0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ budget

def cappedSlope (cap w : Fin 2 → Rat) (p : Fin 2) : Rat :=
  if w p ≤ cap p then 1 else 0

/-- A supporting supergradient exists at every point of the capped objective. -/
theorem cappedSupportingPlane (cap w x : Fin 2 → Rat) :
    cappedObjective cap x ≤ cappedObjective cap w +
      cappedSlope cap w 0 * (x 0 - w 0) +
      cappedSlope cap w 1 * (x 1 - w 1) := by
  have hpart (p : Fin 2) :
      min (x p) (cap p) ≤ min (w p) (cap p) +
        cappedSlope cap w p * (x p - w p) := by
    by_cases h : w p ≤ cap p
    · by_cases hx : x p ≤ cap p
      · simp [cappedSlope, Rat.min_def, h, hx]
        grind
      · simp [cappedSlope, Rat.min_def, h, hx]
        grind
    · by_cases hx : x p ≤ cap p
      · simp [cappedSlope, Rat.min_def, h, hx]
        grind
      · simp [cappedSlope, Rat.min_def, h, hx]
        grind
  have h0 := hpart 0
  have h1 := hpart 1
  unfold cappedObjective
  grind

/-- The vector `(1,1)` is a supergradient where both pieces are unsaturated. -/
theorem cappedSupergradient (cap w x : Fin 2 → Rat)
    (h0 : w 0 ≤ cap 0) (h1 : w 1 ≤ cap 1) :
    cappedObjective cap x ≤ cappedObjective cap w +
      ((x 0 - w 0) + (x 1 - w 1)) := by
  have hleft0 : min (x 0) (cap 0) ≤ x 0 := by grind [min]
  have hleft1 : min (x 1) (cap 1) ≤ x 1 := by grind [min]
  have hw0 : min (w 0) (cap 0) = w 0 := by grind [min]
  have hw1 : min (w 1) (cap 1) = w 1 := by grind [min]
  simp only [cappedObjective, hw0, hw1]
  grind

/-- Concrete KKT data for unit costs and an unsaturated unit supergradient. -/
structure CappedKKT (cap : Fin 2 → Rat) (budget : Rat)
    (w : Fin 2 → Rat) where
  feasible : cappedFeasible budget w
  unsaturated0 : w 0 ≤ cap 0
  unsaturated1 : w 1 ≤ cap 1
  lambda : Rat
  mu : Fin 2 → Rat
  lambdaNonnegative : 0 ≤ lambda
  muNonnegative : ∀ p, 0 ≤ mu p
  stationarity : ∀ p, (1 : Rat) = lambda - mu p
  complementary0 : mu 0 * w 0 = 0
  complementary1 : mu 1 * w 1 = 0
  budgetComplementary : lambda * (budget - (w 0 + w 1)) = 0

theorem cappedKKT_binding (cap : Fin 2 → Rat) (budget : Rat)
    (w : Fin 2 → Rat) (kkt : CappedKKT cap budget w) :
    w 0 + w 1 = budget := by
  have hstat := kkt.stationarity 0
  have hmu := kkt.muNonnegative 0
  have hpositive : 0 < kkt.lambda := by grind
  have hzero : budget - (w 0 + w 1) = 0 := by
    have hmul := kkt.budgetComplementary
    grind [Rat.mul_eq_zero]
  grind

theorem cappedKKT_sufficient (cap : Fin 2 → Rat) (budget : Rat)
    (w x : Fin 2 → Rat) (kkt : CappedKKT cap budget w)
    (hx : cappedFeasible budget x) :
    cappedObjective cap x ≤ cappedObjective cap w := by
  have hgrad := cappedSupergradient cap w x
    kkt.unsaturated0 kkt.unsaturated1
  have hbudget : x 0 + x 1 ≤ w 0 + w 1 := by
    rw [cappedKKT_binding cap budget w kkt]
    exact hx.2.2
  have hsum : (x 0 - w 0) + (x 1 - w 1) ≤ 0 := by
    grind
  have htotal : cappedObjective cap w +
      ((x 0 - w 0) + (x 1 - w 1)) ≤ cappedObjective cap w := by
    grind
  exact Rat.le_trans hgrad htotal

def cappedKKT_exists (cap : Fin 2 → Rat) (budget : Rat)
    (w : Fin 2 → Rat) (hw : cappedFeasible budget w)
    (h0 : w 0 ≤ cap 0) (h1 : w 1 ≤ cap 1)
    (hbind : w 0 + w 1 = budget) : CappedKKT cap budget w := by
  refine ⟨hw, h0, h1, 1, (fun _ => 0), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · intro p; exact Rat.le_refl
  · intro p; grind
  · simp
  · simp
  · rw [← hbind]
    grind

#print axioms cappedSupergradient
#print axioms cappedSupportingPlane
#print axioms cappedKKT_binding
#print axioms cappedKKT_sufficient
#print axioms cappedKKT_exists

end SixBirdsFoundationsV.Instances
