import SixBirdsFoundationsV.Laws.E13RepairTransport

namespace SixBirdsFoundationsV.Instances

def transportContextZero : TransportContextRecord :=
  { contextId := 0,
    challengeClass := { challengeId := 0, taxonomyId := 0 },
    contextReadout := { readoutId := 0 } }

def transportContextOne : TransportContextRecord :=
  { contextId := 1,
    challengeClass := { challengeId := 0, taxonomyId := 0 },
    contextReadout := { readoutId := 1 } }

def twoTransportContexts : List TransportContextRecord :=
  [transportContextZero, transportContextOne]

theorem E13_two_contexts_distinct :
    transportContextZero ≠ transportContextOne := by
  decide

theorem E13_two_contexts_members :
    transportContextZero ∈ twoTransportContexts ∧
    transportContextOne ∈ twoTransportContexts ∧
    twoTransportContexts.length ≥ 2 := by
  decide

#print axioms E13_two_contexts_distinct
#print axioms E13_two_contexts_members

end SixBirdsFoundationsV.Instances
