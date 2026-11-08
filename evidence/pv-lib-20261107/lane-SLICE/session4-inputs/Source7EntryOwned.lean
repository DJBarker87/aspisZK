import PV_STX2_SliceRootReceived
import
  PV_OWN2_Codec
set_option autoImplicit false
noncomputable section
namespace PV_STX2_Source7EntryOwned
open Aeneas Aeneas.Std ProverRwFull
open PV_EVHB_OWNER PV_EVHB_RawVecOwner
abbrev Foundation := aspis_statement.state_only_trace.StateOnlyTraceFoundation
/-- Conditional on owner acceptance of the translator patch. Pure column values
in original Foundation order, without reducing any M31 representation. -/
def values (foundation : Foundation) (i : Fin foundation.c1.val.length) : List PV_OWN2_Codec.M31 :=
  (foundation.c1.val[i]).val
/-- Conditional on owner acceptance of the translator patch. ENTRY obligation
(slice-1), universally quantified over the OWNER pre-state and Foundation.
The Foundation-construction slice must discharge this obligation using its
actual Vec constructions. It mentions no clone result, allocation reply or q.
The witnesses are fixed at entry, before any instrumented capture is derived. -/
def Source7EntryOwned (s : OWNER) (foundation : Foundation) : Prop :=
  ∀ i : Fin foundation.c1.val.length, ∃ p : Place, ∃ id : Nat, ∃ h : Header,
    s.places p = some id ∧ lookup s.world id = some h ∧
    (values foundation i).length ≤ h.cap ∧ h.shape.width = 4 ∧
    PV_OWN2_Codec.TypedMemory 4 PV_OWN2_Codec.decodeM31 s ⟨p,values foundation i⟩
/-- Conditional on owner acceptance of the translator patch. Named caller
obligation; proving it for the actual Foundation builder belongs to that slice. -/
def FoundationConstructionEntryObligation (s : OWNER) (foundation : Foundation) : Prop :=
  Source7EntryOwned s foundation
#print axioms values
#print axioms Source7EntryOwned
#print axioms FoundationConstructionEntryObligation
end PV_STX2_Source7EntryOwned
