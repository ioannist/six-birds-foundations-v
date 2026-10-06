import SixBirdsFoundationsV.Laws.E12Individuation

namespace SixBirdsFoundationsV.Instances.E12Semantic

abbrev Part (α : Type) := α → Prop

def Subset {α : Type} (P Q : Part α) : Prop := ∀ x, P x → Q x

def Inter {α : Type} (P Q : Part α) : Part α := fun x => P x ∧ Q x

def Overlap {α : Type} (P Q : Part α) : Prop := ∃ x, P x ∧ Q x

structure PartClosure (α : Type) where
  close : Part α → Part α
  extensive : ∀ P, Subset P (close P)
  monotone : ∀ ⦃P Q⦄, Subset P Q → Subset (close P) (close Q)
  idempotent : ∀ P, close (close P) = close P

/-- Boundary viability is a finite-system constraint, such as interface capacity. -/
structure System (α : Type) where
  finite : ∃ n, ∃ f : Fin n → α, Function.Surjective f
  step : α → α → Prop
  closure : PartClosure α
  boundaryRegions : List (Part α)

/-- Viability is inclusion in one of the system's declared finite boundary regions. -/
def BoundaryViable {α : Type} (S : System α) (P : Part α) : Prop :=
  ∃ R, R ∈ S.boundaryRegions ∧ Subset P R

def RepairClosed {α : Type} (S : System α) (P : Part α) : Prop :=
  S.closure.close P = P ∧ ∀ x y, P x → S.step x y → P y

def SelfMaintaining {α : Type} (S : System α) (P : Part α) : Prop :=
  (∃ x, P x) ∧ BoundaryViable S P ∧
    ∀ x, P x → ∃ y, P y ∧ S.step x y

def Candidate {α : Type} (S : System α) (P : Part α) : Prop :=
  RepairClosed S P ∧ SelfMaintaining S P

def Maximal {α : Type} (S : System α) (P : Part α) : Prop :=
  Candidate S P ∧ ∀ Q, Candidate S Q → Subset P Q → Q = P

def Integrated {α : Type} (S : System α) (P : Part α) : Prop :=
  Maximal S P ∧ ∀ Q, Maximal S Q → Overlap P Q → Q = P

/-- Repair-closed parts form an intersection-closed family. -/
theorem repairClosed_inter {α : Type} (S : System α) {P Q : Part α}
    (hP : RepairClosed S P) (hQ : RepairClosed S Q) :
    RepairClosed S (Inter P Q) := by
  constructor
  · funext x
    apply propext
    constructor
    · intro hx
      have hp := S.closure.monotone (P := Inter P Q) (Q := P)
        (by intro y hy; exact hy.1)
      have hq := S.closure.monotone (P := Inter P Q) (Q := Q)
        (by intro y hy; exact hy.2)
      rw [hP.1] at hp
      rw [hQ.1] at hq
      exact ⟨hp x hx, hq x hx⟩
    · exact S.closure.extensive _ x
  · intro x y hx hxy
    exact ⟨hP.2 x y hx.1 hxy, hQ.2 x y hx.2 hxy⟩

/-- Distinct integrated individuals have no state in common. -/
theorem integrated_disjoint_or_equal {α : Type} (S : System α)
    {P Q : Part α} (hP : Integrated S P) (hQ : Integrated S Q) :
    P = Q ∨ ¬ Overlap P Q := by
  by_cases h : Overlap P Q
  · exact Or.inl ((hP.2 Q hQ.1 h).symm)
  · exact Or.inr h

def identityClosure (α : Type) : PartClosure α where
  close := id
  extensive := by intro P x hx; exact hx
  monotone := by intro P Q h; exact h
  idempotent := by intro P; rfl

/-- The permitted region is a proper two-state component. -/
def firstPart : Part (Fin 3) := fun x => x = 0 ∨ x = 1

def firstSystem : System (Fin 3) where
  finite := ⟨3, id, by intro x; exact ⟨x, rfl⟩⟩
  step := fun x y => (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0) ∨ (x = 2 ∧ y = 2)
  closure := identityClosure _
  boundaryRegions := [firstPart]

private theorem identity_candidate {α : Type} (S : System α)
    (hs : S.step = Eq) (hc : S.closure = identityClosure α)
    {P : Part α} (hn : ∃ x, P x) (hb : BoundaryViable S P) :
    Candidate S P := by
  constructor
  · constructor
    · rw [hc]; rfl
    · intro x y hx hxy; rw [hs] at hxy; exact hxy ▸ hx
  · exact ⟨hn, hb, by intro x hx; exact ⟨x, hx, by rw [hs]⟩⟩

theorem firstPart_candidate : Candidate firstSystem firstPart := by
  constructor
  · constructor
    · rfl
    · intro x y hx hxy
      rcases hxy with ⟨_, hy⟩ | ⟨_, hy⟩ | ⟨hx2, _⟩
      · exact Or.inr hy
      · exact Or.inl hy
      · subst x
        have hf : False := by simp [firstPart] at hx
        exact hf.elim
  · refine ⟨⟨0, Or.inl rfl⟩, ⟨firstPart, by simp [firstSystem], fun _ h => h⟩, ?_⟩
    intro x hx
    rcases hx with h | h
    · exact ⟨1, Or.inr rfl, Or.inl ⟨h, rfl⟩⟩
    · exact ⟨0, Or.inl rfl, Or.inr (Or.inl ⟨h, rfl⟩)⟩

theorem firstPart_integrated : Integrated firstSystem firstPart := by
  have hm : Maximal firstSystem firstPart := by
    refine ⟨firstPart_candidate, ?_⟩
    intro Q hQ hsub
    funext x
    apply propext
    constructor
    · rcases hQ.2.2.1 with ⟨R, hR, hsubR⟩
      have hEq : R = firstPart := by simpa [firstSystem] using hR
      rw [hEq] at hsubR
      exact hsubR x
    · exact hsub x
  refine ⟨hm, ?_⟩
  intro Q hQ _
  have hsub : Subset Q firstPart := by
    rcases hQ.1.2.2.1 with ⟨R, hR, hQR⟩
    have hEq : R = firstPart := by simpa [firstSystem] using hR
    rw [hEq] at hQR
    exact hQR
  exact (hQ.2 firstPart firstPart_candidate hsub).symm

theorem firstPart_nontrivial :
    (∃ x, firstPart x) ∧ (∃ x, ¬ firstPart x) := by
  exact ⟨⟨0, Or.inl rfl⟩, ⟨2, by simp [firstPart]⟩⟩

def secondLeft : Part (Fin 3) := fun x => x = 0 ∨ x = 1
def secondRight : Part (Fin 3) := fun x => x = 1 ∨ x = 2

/-- Two permitted components overlap at state 1, with no permitted union. -/
def secondSystem : System (Fin 3) where
  finite := ⟨3, id, by intro x; exact ⟨x, rfl⟩⟩
  step := Eq
  closure := identityClosure _
  boundaryRegions := [secondLeft, secondRight]

theorem secondLeft_candidate : Candidate secondSystem secondLeft := by
  apply identity_candidate secondSystem rfl rfl
  · exact ⟨0, Or.inl rfl⟩
  · exact ⟨secondLeft, by simp [secondSystem], fun _ h => h⟩

theorem secondRight_candidate : Candidate secondSystem secondRight := by
  apply identity_candidate secondSystem rfl rfl
  · exact ⟨2, Or.inr rfl⟩
  · exact ⟨secondRight, by simp [secondSystem], fun _ h => h⟩

theorem secondLeft_maximal : Maximal secondSystem secondLeft := by
  refine ⟨secondLeft_candidate, ?_⟩
  intro Q hQ hsub
  rcases hQ.2.2.1 with ⟨R, hR, hQR⟩
  have hRegions : R = secondLeft ∨ R = secondRight := by
    simpa [secondSystem] using hR
  rcases hRegions with hleft | hright
  · rw [hleft] at hQR
    funext x; apply propext; exact ⟨hQR x, hsub x⟩
  · rw [hright] at hQR
    have hzero := hQR 0 (hsub 0 (Or.inl rfl))
    rcases hzero with h | h <;> contradiction

theorem secondRight_maximal : Maximal secondSystem secondRight := by
  refine ⟨secondRight_candidate, ?_⟩
  intro Q hQ hsub
  rcases hQ.2.2.1 with ⟨R, hR, hQR⟩
  have hRegions : R = secondLeft ∨ R = secondRight := by
    simpa [secondSystem] using hR
  rcases hRegions with hleft | hright
  · rw [hleft] at hQR
    have htwo := hQR 2 (hsub 2 (Or.inr rfl))
    rcases htwo with h | h <;> contradiction
  · rw [hright] at hQR
    funext x; apply propext; exact ⟨hQR x, hsub x⟩

theorem second_no_integrated : ¬ ∃ P, Integrated secondSystem P := by
  rintro ⟨P, hP⟩
  rcases hP.1.1.2.2.1 with ⟨R, hR, hPR⟩
  have hRegions : R = secondLeft ∨ R = secondRight := by
    simpa [secondSystem] using hR
  rcases hRegions with hleft | hright
  · have hp : P = secondLeft :=
      (hP.1.2 secondLeft secondLeft_candidate (hleft ▸ hPR)).symm
    have hover : Overlap P secondRight := by
      rw [hp]; exact ⟨1, Or.inr rfl, Or.inl rfl⟩
    have heq := hP.2 secondRight secondRight_maximal hover
    have hzero : secondRight 0 := by rw [heq.trans hp]; exact Or.inl rfl
    rcases hzero with h | h <;> contradiction
  · have hp : P = secondRight := (hP.1.2 secondRight secondRight_candidate (hright ▸ hPR)).symm
    have hover : Overlap P secondLeft := by
      rw [hp]; exact ⟨1, Or.inl rfl, Or.inr rfl⟩
    have heq := hP.2 secondLeft secondLeft_maximal hover
    have htwo : secondLeft 2 := by rw [heq.trans hp]; exact Or.inr rfl
    rcases htwo with h | h <;> contradiction

/-- A damaged component is tied to its healthy repair state; `outside` is a
separate component. Saturation adds either endpoint of a repair pair whenever
the other endpoint is present. Thus it adds repair targets and repair sources. -/
inductive RepairState where
  | healthy | damaged | outside
  deriving DecidableEq

def repairSaturation (P : Part RepairState) : Part RepairState
  | .healthy => P .healthy ∨ P .damaged
  | .damaged => P .healthy ∨ P .damaged
  | .outside => P .outside

def genuineRepairClosure : PartClosure RepairState where
  close := repairSaturation
  extensive := by
    intro P x hx
    cases x with
    | healthy => exact Or.inl hx
    | damaged => exact Or.inr hx
    | outside => exact hx
  monotone := by
    intro P Q h x hx
    cases x with
    | healthy =>
        rcases hx with hp | hp
        · exact Or.inl (h _ hp)
        · exact Or.inr (h _ hp)
    | damaged =>
        rcases hx with hp | hp
        · exact Or.inl (h _ hp)
        · exact Or.inr (h _ hp)
    | outside => exact h _ hx
  idempotent := by
    intro P
    funext x
    cases x <;> apply propext <;> simp [repairSaturation]

def repairPart : Part RepairState :=
  fun x => x = .healthy ∨ x = .damaged

def healthyOnly : Part RepairState := fun x => x = .healthy

/-- Perturbation is external to the endogenous repair relation used by
`RepairClosed`; damaged-to-healthy repair and stuttering are endogenous steps. -/
def perturbation (x y : RepairState) : Prop :=
  x = .healthy ∧ y = .damaged

def endogenousRepair (x y : RepairState) : Prop :=
  x = .damaged ∧ y = .healthy

def repairSystem : System RepairState where
  finite := ⟨3, (fun i => if i = 0 then .healthy else if i = 1 then .damaged else .outside), by
    intro x
    cases x with
    | healthy => exact ⟨0, by decide⟩
    | damaged => exact ⟨1, by decide⟩
    | outside => exact ⟨2, by decide⟩⟩
  step := fun x y => x = y ∨ endogenousRepair x y
  closure := genuineRepairClosure
  boundaryRegions := [repairPart]

theorem repairSystem_has_perturbation :
    perturbation .healthy .damaged := ⟨rfl, rfl⟩

theorem repairSystem_has_repair :
    repairSystem.step .damaged .healthy := Or.inr ⟨rfl, rfl⟩

theorem repairPart_candidate : Candidate repairSystem repairPart := by
  constructor
  · constructor
    · funext x
      change repairSaturation repairPart x = repairPart x
      cases x <;> apply propext <;> simp [repairSaturation, repairPart]
    · intro x y hx hxy
      rcases hxy with h | ⟨_, hy⟩
      · exact h ▸ hx
      · exact Or.inl hy
  · exact ⟨⟨.healthy, Or.inl rfl⟩,
      ⟨repairPart, by simp [repairSystem], fun _ h => h⟩,
      by intro x hx; exact ⟨x, hx, Or.inl rfl⟩⟩

theorem repairPart_integrated : Integrated repairSystem repairPart := by
  have hm : Maximal repairSystem repairPart := by
    refine ⟨repairPart_candidate, ?_⟩
    intro Q hQ hsub
    rcases hQ.2.2.1 with ⟨R, hR, hQR⟩
    have hEq : R = repairPart := by simpa [repairSystem] using hR
    rw [hEq] at hQR
    funext x
    apply propext
    exact ⟨hQR x, hsub x⟩
  refine ⟨hm, ?_⟩
  intro Q hQ _
  rcases hQ.1.2.2.1 with ⟨R, hR, hQR⟩
  have hEq : R = repairPart := by simpa [repairSystem] using hR
  rw [hEq] at hQR
  exact (hQ.2 repairPart repairPart_candidate hQR).symm

theorem repairPart_contains_damage_and_repair :
    repairPart .damaged ∧ repairPart .healthy ∧
      endogenousRepair .damaged .healthy ∧
      repairSystem.step .damaged .healthy := by
  exact ⟨Or.inr rfl, Or.inl rfl, ⟨rfl, rfl⟩, repairSystem_has_repair⟩

theorem repairPart_nontrivial :
    (∃ x, repairPart x) ∧ (∃ x, ¬ repairPart x) := by
  exact ⟨⟨.damaged, Or.inr rfl⟩, ⟨.outside, by simp [repairPart]⟩⟩

theorem healthyOnly_invariant :
    ∀ x y, healthyOnly x → repairSystem.step x y → healthyOnly y := by
  intro x y hx hxy
  rcases hxy with h | ⟨hDamaged, _⟩
  · exact h ▸ hx
  · have : False := by simp [healthyOnly] at hx; cases hx; cases hDamaged
    exact this.elim

theorem healthyOnly_selfMaintaining : SelfMaintaining repairSystem healthyOnly := by
  refine ⟨⟨.healthy, rfl⟩, ?_, ?_⟩
  · exact ⟨repairPart, by simp [repairSystem], by
      intro x hx; exact Or.inl hx⟩
  · intro x hx
    exact ⟨x, hx, Or.inl rfl⟩

theorem healthyOnly_not_closureFixed :
    repairSystem.closure.close healthyOnly ≠ healthyOnly := by
  intro heq
  have hDamaged : repairSystem.closure.close healthyOnly .damaged :=
    Or.inl rfl
  rw [heq] at hDamaged
  cases hDamaged

theorem healthyOnly_not_candidate : ¬ Candidate repairSystem healthyOnly := by
  intro h
  exact healthyOnly_not_closureFixed h.1.1

theorem repairedIndividualWitness :
    Integrated repairSystem repairPart ∧
    repairPart .damaged ∧ repairPart .healthy ∧
    endogenousRepair .damaged .healthy ∧
    repairPart ≠ (fun _ => False) ∧
    repairPart ≠ (fun _ => True) := by
  refine ⟨repairPart_integrated, ?_, ?_, ?_, ?_, ?_⟩
  · exact repairPart_contains_damage_and_repair.1
  · exact repairPart_contains_damage_and_repair.2.1
  · exact repairPart_contains_damage_and_repair.2.2.1
  · intro h
    have hd : repairPart .damaged := repairPart_contains_damage_and_repair.1
    rw [h] at hd
    exact hd
  · intro h
    have ho : repairPart .outside := h ▸ True.intro
    simp [repairPart] at ho

theorem healthyOnly_closure_loadBearing :
    (∀ x y, healthyOnly x → repairSystem.step x y → healthyOnly y) ∧
    SelfMaintaining repairSystem healthyOnly ∧
    ¬ Candidate repairSystem healthyOnly :=
  ⟨healthyOnly_invariant, healthyOnly_selfMaintaining,
    healthyOnly_not_candidate⟩

#print axioms repairClosed_inter
#print axioms integrated_disjoint_or_equal
#print axioms firstPart_integrated
#print axioms firstPart_nontrivial
#print axioms secondLeft_maximal
#print axioms secondRight_maximal
#print axioms second_no_integrated
#print axioms genuineRepairClosure
#print axioms repairSystem_has_perturbation
#print axioms repairSystem_has_repair
#print axioms repairPart_integrated
#print axioms repairPart_contains_damage_and_repair
#print axioms repairPart_nontrivial
#print axioms healthyOnly_invariant
#print axioms healthyOnly_selfMaintaining
#print axioms healthyOnly_not_closureFixed
#print axioms healthyOnly_not_candidate
#print axioms repairedIndividualWitness
#print axioms healthyOnly_closure_loadBearing

end SixBirdsFoundationsV.Instances.E12Semantic
