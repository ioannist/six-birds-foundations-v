import SixBirdsFoundationsV.Instances.E1ExecutedFamily

namespace SixBirdsFoundationsV.Instances

/-- The certified schema quantifies over arbitrary families, including the empty one.
Consequently perpetual novelty is inconsistent independently of the trajectory. -/
theorem finiteForcingNoPerpetualNovelty
    {System : Type u} {History : Type v} {ChallengeClass : Type w}
    {Sigma : Type x} {Entry : Type y} {X : Type z}
    {Refinement : Type r}
    (forcing : FiniteForcingStrictnessCertified System History ChallengeClass
      Sigma Entry X Refinement)
    (S : System) (H : History) (C : ChallengeClass)
    (Sigma_at : Nat → Sigma)
    (generic : GenericallyNovelChallenge ChallengeClass Sigma)
    (strict : StrictSelfExtension (X → Refinement) Sigma)
    (novel : ∀ t, generic.holds C (Sigma_at t)) : False := by
  have h := forcing.strictExtensions S H C Sigma_at
    (fun _ => none) generic strict novel
  obtain ⟨t, entry, R, _, hentry, _⟩ := h 0
  cases hentry

/-- This applies to the task-5 device, but also to any infinite recurring family. -/
theorem eventNoPerpetualNovelty {Sigma : Type}
    (forcing : FiniteForcingStrictnessCertified
      (ESystem.{0,0,0,0,0,0,0,0,0,0,0}
        Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit)
      (ChallengeHistory Unit Unit Unit Unit Unit Unit Unit Unit)
      Unit Sigma (RepairTypedAuditEntry Unit Unit Unit) Bool Bool)
    (Sigma_at : Nat → Sigma)
    (generic : GenericallyNovelChallenge Unit Sigma)
    (strict : StrictSelfExtension (Bool → Bool) Sigma)
    (novel : ∀ t, generic.holds () (Sigma_at t)) : False :=
  finiteForcingNoPerpetualNovelty forcing eventSystem eventHistory ()
    Sigma_at generic strict novel

/-- The schema ranges over every novelty test as well as every family. Choosing
an always-true test and the empty family makes the certificate impossible on
inhabited carriers, without any premise about an actual run. -/
theorem finiteForcingUninhabited
    {System : Type u} {History : Type v} {ChallengeClass : Type w}
    {Sigma : Type x} {Entry : Type y} {X : Type z}
    {Refinement : Type r}
    [Nonempty System] [Nonempty History] [Nonempty ChallengeClass]
    [Nonempty Sigma] :
    FiniteForcingStrictnessCertified System History ChallengeClass
      Sigma Entry X Refinement → False := by
  intro forcing
  let S : System := Classical.choice inferInstance
  let H : History := Classical.choice inferInstance
  let C : ChallengeClass := Classical.choice inferInstance
  let sigma : Sigma := Classical.choice inferInstance
  let generic : GenericallyNovelChallenge ChallengeClass Sigma :=
    ⟨fun _ _ => True⟩
  let strict : StrictSelfExtension (X → Refinement) Sigma :=
    ⟨fun _ _ => False⟩
  have h := forcing.strictExtensions S H C (fun _ => sigma)
    (fun _ => none) generic strict (by intro t; trivial)
  obtain ⟨_, _, _, _, hEntry, _⟩ := h 0
  cases hEntry

/-- In particular the certificate required by `E1_StrictSelfExtension` has
no inhabitant whenever its system, history, class and state types do. -/
theorem E1_StrictSelfExtension_noCertificate
    {System : Type u} {History : Type v} {ChallengeClass : Type w}
    {Sigma : Type x} {Entry : Type y} {X : Type z}
    {Refinement : Type r}
    [Nonempty System] [Nonempty History] [Nonempty ChallengeClass]
    [Nonempty Sigma] :
    ¬ FiniteForcingStrictnessCertified System History ChallengeClass
      Sigma Entry X Refinement :=
  finiteForcingUninhabited

#print axioms finiteForcingNoPerpetualNovelty
#print axioms eventNoPerpetualNovelty
#print axioms finiteForcingUninhabited
#print axioms E1_StrictSelfExtension_noCertificate

end SixBirdsFoundationsV.Instances
