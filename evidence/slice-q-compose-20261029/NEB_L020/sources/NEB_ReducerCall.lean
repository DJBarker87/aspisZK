import NEB_Reference.Funs
import NEB_BaseCallBounds
set_option autoImplicit false
namespace NEB_ReducerCall
open Aeneas Aeneas.Std Result AspisR1

def PacketDomain (x : U64) : Prop := x.val<18446744073709551616

theorem all_domain (x : U64) : PacketDomain x := by
  unfold PacketDomain
  scalar_tac

/-- Exact independently extracted scalar reference, not a value-only or
success-conditioned comparison. -/
theorem reference (x : U64) :
    NEB_Reference.reference x=FIo_Native.aspis_core.field.reduce_u64 x := by
  simp only [NEB_Reference.reference,NEB_Reference.P,
    FIo_Native.aspis_core.field.reduce_u64,FIo_Native.aspis_core.field.P,
    core.num.U64.wrapping_add,core.num.U32.wrapping_sub,
    U64.wrapping_add,U32.wrapping_sub,U64.wrapping_shr,lift,bind_tc_ok]
  rfl

theorem wrapper (x : U64) :
    FIo_Native.aspis_core.field.M31.reduce_u64 x=NEB_Reference.reference x := by
  rw [reference]
  exact NEB_BaseCallBounds.reducer_wrapper x

/-- There is no strengthened canonical-input assumption at this edge. -/
theorem value (x : U64) : ∃ z : U32,
    NEB_Reference.reference x=ok z ∧
    FIo_Native.aspis_core.field.M31.reduce_u64 x=ok z ∧
    z.val=x.val%2147483647 ∧ z.val<2147483647 := by
  obtain ⟨z,run,value,canonical⟩ := LPf_CoreReduction.source x
  exact ⟨z,(reference x).trans run,(wrapper x).trans ((reference x).trans run),value,canonical⟩

def withState {S Event : Type} (s : S) (r : Result U32) : Result (U32 × S × List Event) := do
  let z ← r
  ok (z,s,[])

/-- Pure scalar execution lifts uniformly to any ambient state and event
carrier. Native purity is checked separately against the frozen body and
contract; this lemma does not define a new native evaluator. -/
theorem state_effects {S Event : Type} (s : S) (x : U64) :
    ∃ z : U32,
      withState (Event:=Event) s (NEB_Reference.reference x)=ok (z,s,[]) ∧
      withState (Event:=Event) s (FIo_Native.aspis_core.field.M31.reduce_u64 x)=ok (z,s,[]) ∧
      z.val=x.val%2147483647 ∧ z.val<2147483647 := by
  obtain ⟨z,ref,root,value,canonical⟩ := value x
  exact ⟨z,by simp only [withState,ref,bind_tc_ok],by simp only [withState,root,bind_tc_ok],value,canonical⟩

#print axioms all_domain
#print axioms reference
#print axioms wrapper
#print axioms value
#print axioms state_effects
end NEB_ReducerCall
