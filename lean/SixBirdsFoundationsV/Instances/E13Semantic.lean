import SixBirdsFoundationsV.Laws.E13RepairTransport

namespace SixBirdsFoundationsV.Instances.E13Semantic

/-- A context-indexed repair relation and obstruction measure. -/
structure System (State Context : Type) where
  repair : Context → State → State → Prop
  obstruction : Context → State → Nat
  challengeClass : Context → Nat
  role : State → Nat

/-- A paid interface maps repair states and contexts while preserving their roles
and challenge classes. The cost is the interface payment. -/
structure Interface (A : System SA CA) (B : System SB CB) where
  onState : SA → SB
  onContext : CA → CB
  payment : Nat
  paid : 0 < payment
  roles : ∀ s, B.role (onState s) = A.role s
  classes : ∀ c, B.challengeClass (onContext c) = A.challengeClass c

/-- Every source repair must become a receiver repair with a strict decrease of
obstruction in the preserved challenge class. -/
structure RepairTransport (A : System SA CA) (B : System SB CB) where
  interface : Interface A B
  mapsRepair : ∀ c s t, A.repair c s t →
    B.repair (interface.onContext c) (interface.onState s) (interface.onState t)
  reduces : ∀ c s t, A.repair c s t →
    B.obstruction (interface.onContext c) (interface.onState t) <
      B.obstruction (interface.onContext c) (interface.onState s)

/-- Paid repair transports compose; the interface payments add. -/
def compose {A : System SA CA} {B : System SB CB} {C : System SC CC}
    (f : RepairTransport A B) (g : RepairTransport B C) : RepairTransport A C where
  interface := {
    onState := g.interface.onState ∘ f.interface.onState
    onContext := g.interface.onContext ∘ f.interface.onContext
    payment := f.interface.payment + g.interface.payment
    paid := by have hf := f.interface.paid; have hg := g.interface.paid; omega
    roles := by intro s; exact (g.interface.roles (f.interface.onState s)).trans (f.interface.roles s)
    classes := by intro c; exact (g.interface.classes (f.interface.onContext c)).trans (f.interface.classes c) }
  mapsRepair := by
    intro c s t h
    exact g.mapsRepair _ _ _ (f.mapsRepair c s t h)
  reduces := by
    intro c s t h
    exact g.reduces _ _ _ (f.mapsRepair c s t h)

theorem compose_payment {A : System SA CA} {B : System SB CB}
    {C : System SC CC} (f : RepairTransport A B)
    (g : RepairTransport B C) :
    (compose f g).interface.payment = f.interface.payment + g.interface.payment := rfl

/-- Two different contexts share challenge class 7 but have different offsets. -/
def source : System Nat (Fin 2) where
  repair := fun _ s t => t < s
  obstruction := fun c s => s + c.val
  challengeClass := fun _ => 7
  role := fun s => s % 2

def receiver : System Nat (Fin 2) where
  repair := fun _ s t => t < s
  obstruction := fun c s => s + c.val + 1
  challengeClass := fun _ => 7
  role := fun s => s % 2

def third : System Nat (Fin 2) where
  repair := fun _ s t => t < s
  obstruction := fun c s => s + c.val + 2
  challengeClass := fun _ => 7
  role := fun s => s % 2

def sourceToReceiver : RepairTransport source receiver where
  interface := {
    onState := id
    onContext := id
    payment := 2
    paid := by decide
    roles := by intro s; rfl
    classes := by intro c; rfl }
  mapsRepair := by intro c s t h; exact h
  reduces := by
    intro c s t h
    change t < s at h
    change t + c.val + 1 < s + c.val + 1
    omega

def receiverToThird : RepairTransport receiver third where
  interface := {
    onState := id
    onContext := id
    payment := 3
    paid := by decide
    roles := by intro s; rfl
    classes := by intro c; rfl }
  mapsRepair := by intro c s t h; exact h
  reduces := by
    intro c s t h
    change t < s at h
    change t + c.val + 2 < s + c.val + 2
    omega

theorem contexts_distinct : (0 : Fin 2) ≠ 1 := by decide

theorem repairs_in_two_contexts :
    source.repair 0 2 1 ∧ source.repair 1 2 1 ∧
    receiver.obstruction 0 1 < receiver.obstruction 0 2 ∧
    receiver.obstruction 1 1 < receiver.obstruction 1 2 := by
  simp [source, receiver]

theorem concrete_composite_payment :
    (compose sourceToReceiver receiverToThird).interface.payment = 5 := by
  decide

theorem concrete_composite_reduces (c : Fin 2) :
    third.obstruction c 1 < third.obstruction c 2 :=
  (compose sourceToReceiver receiverToThird).reduces c 2 1 (by change (1 : Nat) < 2; omega)

/-- A role-preserving paid map may fail to transport repair. -/
def flatReceiver : System Nat (Fin 2) where
  repair := fun _ s t => t < s
  obstruction := fun _ _ => 0
  challengeClass := fun _ => 7
  role := fun s => s % 2

def roleOnlyInterface : Interface source flatReceiver where
  onState := id
  onContext := id
  payment := 1
  paid := by decide
  roles := by intro s; rfl
  classes := by intro c; rfl

theorem roleOnly_mapsRepair (c : Fin 2) (s t : Nat)
    (h : source.repair c s t) :
    flatReceiver.repair (roleOnlyInterface.onContext c)
      (roleOnlyInterface.onState s) (roleOnlyInterface.onState t) := h

theorem roleOnly_no_reduction :
    ¬ (∀ c s t, source.repair c s t →
      flatReceiver.obstruction (roleOnlyInterface.onContext c)
        (roleOnlyInterface.onState t) <
      flatReceiver.obstruction (roleOnlyInterface.onContext c)
        (roleOnlyInterface.onState s)) := by
  intro h
  have hf := h 0 2 1 (by change (1 : Nat) < 2; omega)
  exact (Nat.not_lt_zero 0) hf

/-- A finite chain records its source and target as well as its exact number
of source repair steps. -/
inductive RepairChain {SA CA : Type} (A : System SA CA) (c : CA) :
    SA → SA → Nat → Prop where
  | nil (s : SA) : RepairChain A c s s 0
  | cons {s t u : SA} {k : Nat} (head : A.repair c s t)
      (tail : RepairChain A c t u k) : RepairChain A c s u (k + 1)

/-- Every transported repair consumes at least one unit of receiver
obstruction, so a chain of length k consumes at least k units. -/
theorem chain_obstruction_bound {A : System SA CA} {B : System SB CB}
    (f : RepairTransport A B) {c : CA} {s t : SA} {k : Nat}
    (h : RepairChain A c s t k) :
    B.obstruction (f.interface.onContext c) (f.interface.onState t) + k ≤
      B.obstruction (f.interface.onContext c) (f.interface.onState s) := by
  induction h with
  | nil s => simp
  | cons head tail ih =>
      have hd := f.reduces _ _ _ head
      omega

theorem chain_length_bound {A : System SA CA} {B : System SB CB}
    (f : RepairTransport A B) {c : CA} {s t : SA} {k : Nat}
    (h : RepairChain A c s t k) :
    k ≤ B.obstruction (f.interface.onContext c) (f.interface.onState s) := by
  have hb := chain_obstruction_bound f h
  omega

/-- The receiver state has an additional carried flag, and its context is
swapped relative to the source. Both contexts remain in challenge class 7. -/
def crossReceiver : System (Nat × Bool) (Fin 2) where
  repair := fun _ s t => t.1 < s.1 ∧ t.2 = s.2
  obstruction := fun c s => s.1 + c.val
  challengeClass := fun _ => 7
  role := fun s => s.1 % 2

def crossTransport : RepairTransport source crossReceiver where
  interface := {
    onState := fun s => (s, true)
    onContext := fun c => if c = 0 then 1 else 0
    payment := 4
    paid := by decide
    roles := by intro s; rfl
    classes := by intro c; rfl }
  mapsRepair := by
    intro c s t h
    exact ⟨h, rfl⟩
  reduces := by
    intro c s t h
    change t < s at h
    change t + (if c = 0 then (1 : Fin 2) else 0).val <
      s + (if c = 0 then (1 : Fin 2) else 0).val
    omega

theorem cross_context_zero_to_one :
    crossTransport.interface.onContext 0 = 1 := by decide

theorem cross_context_one_to_zero :
    crossTransport.interface.onContext 1 = 0 := by decide

theorem cross_state_not_identity_type :
    crossTransport.interface.onState 3 = (3, true) := rfl

def twoStepChain : RepairChain source 0 3 1 2 :=
  .cons (by change (2 : Nat) < 3; omega)
    (.cons (by change (1 : Nat) < 2; omega) (.nil 1))

theorem cross_context_two_step_bound :
    crossReceiver.obstruction (crossTransport.interface.onContext 0)
        (crossTransport.interface.onState 1) + 2 ≤
      crossReceiver.obstruction (crossTransport.interface.onContext 0)
        (crossTransport.interface.onState 3) :=
  chain_obstruction_bound crossTransport twoStepChain

theorem cross_context_two_step_length :
    2 ≤ crossReceiver.obstruction (crossTransport.interface.onContext 0)
      (crossTransport.interface.onState 3) :=
  chain_length_bound crossTransport twoStepChain

#print axioms compose
#print axioms compose_payment
#print axioms sourceToReceiver
#print axioms receiverToThird
#print axioms contexts_distinct
#print axioms repairs_in_two_contexts
#print axioms concrete_composite_payment
#print axioms concrete_composite_reduces
#print axioms roleOnly_mapsRepair
#print axioms roleOnly_no_reduction
#print axioms chain_obstruction_bound
#print axioms chain_length_bound
#print axioms crossTransport
#print axioms cross_context_zero_to_one
#print axioms cross_context_one_to_zero
#print axioms cross_state_not_identity_type
#print axioms twoStepChain
#print axioms cross_context_two_step_bound
#print axioms cross_context_two_step_length

end SixBirdsFoundationsV.Instances.E13Semantic
