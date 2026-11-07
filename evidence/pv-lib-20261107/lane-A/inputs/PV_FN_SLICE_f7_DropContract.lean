import PV_FN_SLICE_f7_DropStatements
import PV_W1_ArgumentEffects
set_option autoImplicit false
noncomputable section
namespace PV_FN_SLICE_f7_Drop
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OwnerMachine

def w1Entry (x : Cut) : PV_W1_LeafBoundary.Entry :=
  {store := x.s,caller := x.a,parents := x.parents,loops := [],rest := [],
   callee := source,arguments := [x.capture],destination := 0,suspended := []}

/-- Two packages' footprint predicates coincide on the same store and values;
no provider definition or source body is changed. -/
theorem reachable_iff (C : Carrier OWNER Data) (s : Store Data) (w : OWNER)
    (args : List Data) (v : Data) :
    PV_W5_DropLeaf.Reachable C s w args v ↔ PV_W1_ArgumentEffects.Reachable C s w args v := by
  constructor
  · intro h
    induction h with
    | argument v member => exact .argument v member
    | field v child n origin selected ih => exact .field v child n ih selected
    | pointee v child p origin address read ih => exact .pointee v child p ih address read
  · intro h
    induction h with
    | argument v member => exact .argument v member
    | field v child n origin selected ih => exact .field v child n ih selected
    | pointee v child p origin address read ih => exact .pointee v child p ih address read

theorem writable_iff (x : Cut) (p : Address) :
    PV_W5_DropLeaf.Writable (PV_FN_SLICE_ValueCarrier.carrier x.C) (entry x) x.w x.capture p ↔
    PV_W1_ArgumentEffects.Writable (PV_FN_SLICE_ValueCarrier.carrier x.C) (w1Entry x) x.w p := by
  constructor <;> rintro ⟨v,q,h,d,r⟩
  · exact ⟨v,q,(reachable_iff _ _ _ _ _).mp h,d,r⟩
  · exact ⟨v,q,(reachable_iff _ _ _ _ _).mpr h,d,r⟩

/-- Instantiation of CLOSED W5 Drop at f7's source178 with its complete delta.
Owner invariants come from the provider's framed lift for EVERY answer. -/
theorem contract : Contract := by
  intro x H changes pre
  have providerPre : PV_W5_LeafBoundary.Pre (entry x) x.w := ⟨pre.1,pre.2⟩
  have provider := PV_W5_DropLeaf.contract (PV_FN_SLICE_ValueCarrier.carrier x.C)
    (entry x) H x.w source x.capture changes providerPre
  refine ⟨provider,rfl,?_,rfl,rfl⟩
  exact ⟨provider.2.2.2.1.identities,provider.2.2.2.1.activations⟩

/-- Full post-store frame is the provider's frame, never an entry-store
replacement. This applies equally to returned, failure, fault and pending. -/
theorem frame (x : Cut) (changes : Address → Option Data) (p : Address)
    (outside : ¬ PV_W1_ArgumentEffects.Writable
      (PV_FN_SLICE_ValueCarrier.carrier x.C) (w1Entry x) x.w p) :
    (effects x changes).cells p = x.s.cells p := by
  exact PV_W5_DropLeaf.outside _ _ _ _ _ _ (fun h => outside ((writable_iff x p).mp h))

/-- INTERNAL preservation lemma: isolation must be DERIVED from the typed
capture/provider, not added to f7's entry or native-reply hypotheses. -/
theorem local0 (x : Cut) (changes : Address → Option Data) (v : Data)
    (before : x.s.cells ⟨x.a,0,[]⟩ = some v)
    (outside : ¬ PV_W1_ArgumentEffects.Writable
      (PV_FN_SLICE_ValueCarrier.carrier x.C) (w1Entry x) x.w ⟨x.a,0,[]⟩) :
    (effects x changes).cells ⟨x.a,0,[]⟩ = some v :=
  (frame x changes _ outside).trans before

/-- The actual emitted drop selects LOCAL1's initialized capture, not a
reference invented by the consumer. A missing capture remains an obligation. -/
theorem operand (x : Cut) (initialized : x.s.cells ⟨x.a,1,[]⟩ = some x.capture) :
    PV_STX2_Store.read (PV_FN_SLICE_ValueCarrier.carrier x.C) x.s x.w x.a (.local 1) = some x.capture := by
  simpa only [PV_STX2_Store.read,locate,readAddress] using initialized

#print axioms reachable_iff
#print axioms writable_iff
#print axioms contract
#print axioms frame
#print axioms local0
#print axioms operand
set_option pp.fullNames true in
set_option pp.proofs false in
#print contract
end PV_FN_SLICE_f7_Drop
