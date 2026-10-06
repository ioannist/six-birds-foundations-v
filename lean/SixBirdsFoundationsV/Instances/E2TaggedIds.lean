import SixBirdsFoundationsV.Laws.E2BoundedReflexivity

namespace SixBirdsFoundationsV.Instances

def TaggedRecordId (InstrumentRecord LedgerEntry AuditRecord : Type) :=
  Sum InstrumentRecord (Sum LedgerEntry AuditRecord)

def instrumentId {I L A : Type} (r : I) : TaggedRecordId I L A := .inl r
def ledgerId {I L A : Type} (r : L) : TaggedRecordId I L A := .inr (.inl r)
def auditId {I L A : Type} (r : A) : TaggedRecordId I L A := .inr (.inr r)

theorem E2_instrument_ids_injective {I L A : Type} {a b : I}
    (h : (instrumentId (L := L) (A := A) a) = instrumentId b) : a = b := by
  cases h
  rfl

theorem E2_ledger_ids_injective {I L A : Type} {a b : L}
    (h : (ledgerId (I := I) (A := A) a) = ledgerId b) : a = b := by
  cases h
  rfl

theorem E2_audit_ids_injective {I L A : Type} {a b : A}
    (h : (auditId (I := I) (L := L) a) = auditId b) : a = b := by
  cases h
  rfl

theorem E2_instrument_ledger_disjoint {I L A : Type} (i : I) (l : L) :
    instrumentId (A := A) i ≠ ledgerId l := by
  intro h
  cases h

theorem E2_instrument_audit_disjoint {I L A : Type} (i : I) (a : A) :
    instrumentId (L := L) i ≠ auditId a := by
  intro h
  cases h

theorem E2_ledger_audit_disjoint {I L A : Type} (l : L) (a : A) :
    ledgerId (I := I) l ≠ auditId a := by
  intro h
  cases h

#print axioms E2_instrument_ids_injective
#print axioms E2_ledger_ids_injective
#print axioms E2_audit_ids_injective
#print axioms E2_instrument_ledger_disjoint
#print axioms E2_instrument_audit_disjoint
#print axioms E2_ledger_audit_disjoint

end SixBirdsFoundationsV.Instances
