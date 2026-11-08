import PV_LIB_A_ScopeIncrementShape14
import PV_FN_THREAD_f6Interfaces
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_ScopePayloadIdentityGap14
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
open PV_LIB_A_ScopePayloadShape14 PV_FN_THREAD_f6Interfaces

theorem initial (C : Carrier OWNER Data) (b : Bool) (s : Store Data) (a slot : Nat)
    (atomicKind cellKind strong weak thread panicked : Data) :
    ∃ sv wv, At (carrier C b) (stored s a slot atomicKind cellKind strong weak thread panicked 0)
      (root a slot) (PV_THR2_KeyValues.pack PV_THR2_Packet124Aggregate13.source.2.2.1
        [sv,wv,payload atomicKind cellKind thread panicked 0]) := by
  refine ⟨strong,weak,inner atomicKind cellKind strong weak thread panicked 0,?_,rfl⟩
  exact write_same s (root a slot) _

/-- The literal fixed-payload facet cannot be framed across13713's457 source
write. This is a local source-state counterexample, NOT original reachability,
a complete f125/LoopInvariant counterexample or a negation of the joint witness.
A loop snapshot may differ from the original124 payload; restoration or a
mutable ScopeData invariant must be proved rather than assumed. -/
theorem not_fixed_payload (C : Carrier OWNER Data) (b : Bool) (s : Store Data) (a slot : Nat)
    (atomicKind cellKind strong weak thread panicked : Data) :
    ¬ ∃ sv wv, At (carrier C b) (stored s a slot atomicKind cellKind strong weak thread panicked 1)
      (root a slot) (PV_THR2_KeyValues.pack PV_THR2_Packet124Aggregate13.source.2.2.1
        [sv,wv,payload atomicKind cellKind thread panicked 0]) := by
  rintro ⟨sv,wv,value,cell,fields⟩
  change some value = some (PV_THR2_KeyValues.pack PV_THR2_Packet124Aggregate13.source.2.2.1
    [sv,wv,payload atomicKind cellKind thread panicked 0]) at fields
  have eq := Option.some.inj fields
  subst value
  change (stored s a slot atomicKind cellKind strong weak thread panicked 1).cells (root a slot) = _ at cell
  have readback : readAddress (carrier C b)
      (stored s a slot atomicKind cellKind strong weak thread panicked 1) (count a slot) = some (.number 0) := by
    unfold readAddress count
    change ((stored s a slot atomicKind cellKind strong weak thread panicked 1).cells (root a slot)).bind _ = _
    rw [cell]
    rfl
  rw [read_count] at readback
  cases readback

/-- Both the actual named source operation and the failed preservation claim
are retained. No payload/read-only premise is quietly added to a row. -/
theorem checked (C : Carrier OWNER Data) (b : Bool) (s : Store Data) (w : OWNER) (a slot : Nat)
    (atomicKind cellKind strong weak thread panicked : Data) :
    let before := stored s a slot atomicKind cellKind strong weak thread panicked 0
    let after := stored s a slot atomicKind cellKind strong weak thread panicked 1
    PV_LIB_A_ScopeStoreV2.PV_THR2_LibrarySemantics_ScopeIncrement457 (carrier C b)
      [PV_STX2_TypedReferences.reference ⟨a,slot,[2]⟩ .null] before w = some after ∧
    (∃ sv wv, At (carrier C b) before (root a slot)
      (PV_THR2_KeyValues.pack PV_THR2_Packet124Aggregate13.source.2.2.1
        [sv,wv,payload atomicKind cellKind thread panicked 0])) ∧
    ¬ ∃ sv wv, At (carrier C b) after (root a slot)
      (PV_THR2_KeyValues.pack PV_THR2_Packet124Aggregate13.source.2.2.1
        [sv,wv,payload atomicKind cellKind thread panicked 0]) :=
  ⟨PV_LIB_A_ScopeIncrementShape14.increment C b s w a slot atomicKind cellKind strong weak thread panicked,
   initial C b s a slot atomicKind cellKind strong weak thread panicked,
   not_fixed_payload C b s a slot atomicKind cellKind strong weak thread panicked⟩

#print axioms initial
#print axioms not_fixed_payload
#print axioms checked
end PV_LIB_A_ScopePayloadIdentityGap14
