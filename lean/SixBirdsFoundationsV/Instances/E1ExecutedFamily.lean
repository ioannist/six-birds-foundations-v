import SixBirdsFoundationsV.Instances.E3Executed
import SixBirdsFoundationsV.Laws.E1Internalization

namespace SixBirdsFoundationsV.Instances

theorem eventClosedLoop : ClosedLoopScope eventSystem eventHistory := by
  refine ⟨trivial, ?_⟩
  intro entry h
  simp [eventHistory] at h
  rcases h with h | h | h
  · subst entry; exact eventAt ()
  · subst entry; exact eventAt ()
  · subst entry; exact eventAt ()

def eventInstalls : MovePayloadInstallsRefinement Unit (Bool → Bool) where
  holds _ R := R = id

def eventPostState : PostRepairStateForEpisode eventSystem Unit Unit Unit Unit Unit where
  holds z' _ := z' = true

def eventQ : Bool → Unit := fun _ => ()
def eventR : Bool → Bool := id
def eventQNext : Bool → Unit × Bool := fun b => ((), b)

def eventBudget : FamilyBudgetFeasibleInLambda
    (CarriedLedger eventTheory Unit) (RepairTypedAuditEntry Unit Unit Unit)
    (Bool → Bool) where
  holds ledger family := () ∈ ledger.ledgerEntries ∧
    ∀ t entry R, family t = some (entry, R) → t = 0

def eventFamily : Nat → Option (RepairTypedAuditEntry Unit Unit Unit ×
    (Bool → Bool)) :=
  fun t => if t = 0 then some (eventMoveEntry, id) else none

theorem eventChallengeTime (t : Nat) :
    ChallengedEpisodeTime eventHistory () t ↔ t = 0 := by
  constructor
  · rintro ⟨episode, hmem, _, htime, _⟩
    have he : episode = spikeEpisode := by
      simpa [eventHistory] using hmem
    subst episode
    exact htime.symm
  · intro h
    subst t
    exact ⟨spikeEpisode, by simp [eventHistory], rfl, rfl, (), rfl⟩

theorem eventOccurrence :
    EndogenousRepairOccurrence eventSystem eventHistory eventInstalls
      eventPostState () 0 eventMoveEntry eventR := by
  refine ⟨spikeEpisode, by simp [eventHistory],
    by simp [eventHistory, eventMoveEntry], rfl, rfl, rfl,
    ?_, rfl, rfl, rfl, false, true, (), (), ?_, eventRepair,
    ?_, rfl, rfl⟩
  · exact eventClosedLoop.2 eventMoveEntry (by simp [eventHistory, eventMoveEntry])
  · rfl
  · exact ⟨rfl, rfl, rfl, Or.inl ⟨rfl, rfl⟩, rfl⟩

theorem eventJoin : InstallsRepairJoin eventQ eventR eventQNext := by
  intro x x'
  constructor
  · intro h
    exact Prod.ext rfl (congrArg Prod.snd h)
  · intro h
    exact h

theorem eventStrictDescent :
    StrictChallengeDescent eventQ eventQNext id id
      (fun _ _ => True) := by
  constructor
  · intro pair h
    exact False.elim (h.1.2 (congrArg Prod.snd h.1.1))
  · refine ⟨(false, true), ?_, ?_⟩
    · exact ⟨⟨rfl, by decide⟩, trivial⟩
    · intro h
      exact h.1.2 (congrArg Prod.snd h.1.1)

theorem eventFamilyAccepted :
    EndogenousRepairFamilyWitness eventSystem eventHistory
      (fun _ => eventQ) (fun _ => eventQNext) id id
      (fun _ _ _ => True) eventInstalls eventPostState eventBudget
      eventFamily () () := by
  refine ⟨⟨0, (eventChallengeTime 0).2 rfl⟩, ?_, ?_, ?_⟩
  · intro t htime
    have ht : t = 0 := (eventChallengeTime t).1 htime
    subst t
    exact ⟨eventMoveEntry, eventR, rfl, eventOccurrence,
      eventJoin, eventStrictDescent⟩
  · intro t entry R hfamily
    have ht : t = 0 := by
      by_cases h : t = 0
      · exact h
      · simp [eventFamily, h] at hfamily
    subst t
    have hpair : (entry, R) = (eventMoveEntry, eventR) := by
      simpa [eventFamily, eventR] using hfamily.symm
    cases hpair
    exact ⟨eventOccurrence, eventJoin, eventStrictDescent⟩
  · constructor
    · decide
    · intro t entry R h
      by_cases ht : t = 0
      · exact ht
      · simp [eventFamily, ht] at h

theorem eventFamilyValid :
    EndogenousRepairFamilyValid eventSystem eventHistory
      (fun _ => eventQ) (fun _ => eventQNext) id id
      (fun _ _ _ => True) eventInstalls eventPostState eventBudget
      () () :=
  ⟨eventFamily, eventFamilyAccepted⟩

/-- A single executed episode cannot meet a perpetual generic-novelty forcing
obligation on this finite family. The finite-forcing premise is used here. -/
theorem eventFiniteForcingRequiresNewEpisodes {Sigma : Type}
    (finiteForcing : FiniteForcingStrictnessCertified
      (ESystem.{0,0,0,0,0,0,0,0,0,0,0}
        Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit)
      (ChallengeHistory Unit Unit Unit Unit Unit Unit Unit Unit)
      Unit Sigma (RepairTypedAuditEntry Unit Unit Unit) Bool Bool)
    (Sigma_at : Nat → Sigma)
    (generic : GenericallyNovelChallenge Unit Sigma)
    (strict : StrictSelfExtension (Bool → Bool) Sigma)
    (hGeneric : ∀ t, generic.holds () (Sigma_at t)) : False := by
  have hInfinite := finiteForcing.strictExtensions eventSystem eventHistory
    () Sigma_at eventFamily generic strict hGeneric
  obtain ⟨t, entry, R, hge, hSome, _⟩ := hInfinite 1
  have ht : t ≠ 0 := by omega
  simp [eventFamily, ht] at hSome

#print axioms eventClosedLoop
#print axioms eventChallengeTime
#print axioms eventOccurrence
#print axioms eventJoin
#print axioms eventStrictDescent
#print axioms eventFamilyAccepted
#print axioms eventFamilyValid
#print axioms eventFiniteForcingRequiresNewEpisodes

end SixBirdsFoundationsV.Instances
