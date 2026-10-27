import R1Z.PV_Src_PortNoop
set_option autoImplicit false
namespace R1Z.PV_Src_PortNoopFull
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_Src_PortTraceRounds

theorem total (kind : Usize → poseidon2.Poseidon2RoundKind)
    (xs : List (Usize × State)) (s input : State) (trace : Unit) (round : U8) :
    ∃ out : Output Unit,
      fullSteps PV_Src_PortNoop.callback kind xs s trace round input = ok out ∧
      out.2.1 = trace := by
  induction xs generalizing s input trace round with
  | nil => exact ⟨(s,trace,round,input),rfl,rfl⟩
  | cons p xs ih =>
    obtain ⟨state1,hstate,_⟩ := full_total s p.2
    obtain ⟨out,ho,htrace⟩ := ih state1 state1 trace (U8.wrapping_add round 1#u8)
    refine ⟨out,?_,htrace⟩
    simp only [fullSteps,hstate,bind_tc_ok,PV_Src_PortNoop.call]
    exact ho

#print axioms total
end R1Z.PV_Src_PortNoopFull
