import PV_EVH_EntropyReturnComplete
set_option autoImplicit false
namespace PV_EVH_EntropyReturnSpatial
open PV_EVH_StackZero (State)
open PV_EVH_EntropyCallerLayout (result)
open PV_EVH_EntropyReturnComplete (finish)

/-- External owners exclude the callee reservation and initialized return
destination. This still permits the caller's live mask input. The reached
call's actual ownership/ABI interpretation remains FRAME-ENTRY/V370. -/
def ExternalByte (sp p : Nat) : Prop :=
  (p < sp ∨ sp+232 ≤ p) ∧ (p < result sp ∨ result sp+97 ≤ p)

theorem outside (owner sp p : Nat) (w : State) (hp : ExternalByte sp p) :
    (finish owner sp w).memory p = w.memory p := by
  unfold finish
  rw [PV_EVH_StackZero.outside_preserved _ _ p (by
    change p < sp ∨ sp+64 ≤ p
    rcases hp.1 with h | h
    · exact Or.inl h
    · exact Or.inr (by omega))]
  exact PV_EVH_EntropyReturnFootprint.outside_writes sp p w hp.1 hp.2

theorem runtime (owner sp : Nat) (w : State) :
    (finish owner sp w).frame.runtime = w.frame.runtime := by
  rw [finish,PV_EVH_StackZero.dropped_runtime]
  exact congrArg (fun f => f.runtime)
    (PV_EVH_StackStores.frame (PV_EVH_EntropyReturnFootprint.stores sp w) w).1

/-- Preservation of all old initialized bytes under the reached-call
external boundary, never preservation of intentionally overwritten return
storage or original64. No assumption of native allocator fidelity is added. -/
theorem live (owner sp : Nat) (w : State)
    (h : ∀ old ∈ w.frame.live, ∀ i, i < old.initialized →
      ExternalByte sp (old.address+i)) :
    ∀ old ∈ w.frame.live, ∀ i, i < old.initialized →
      (finish owner sp w).memory (old.address+i) = w.memory (old.address+i) := by
  intro old ho i hi
  exact outside owner sp _ w (h old ho i hi)

theorem heap (owner sp : Nat) (w : State)
    (hc : PV_EVH_StackAdmission.HeapCoherent w)
    (h : ∀ b ∈ w.frame.runtime.heap, ∀ i, i < b.bytes.length →
      ExternalByte sp (b.address+i)) :
    PV_EVH_StackAdmission.HeapCoherent (finish owner sp w) := by
  intro b hb i hi
  rw [runtime] at hb
  exact (outside owner sp _ w (h b hb i hi)).trans (hc b hb i hi)

#print axioms outside
#print axioms runtime
#print axioms live
#print axioms heap
end PV_EVH_EntropyReturnSpatial
