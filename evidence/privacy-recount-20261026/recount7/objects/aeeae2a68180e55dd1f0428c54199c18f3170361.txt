import R1Z.PV_Src_PortNoop
set_option autoImplicit false
namespace R1Z.PV_Src_PortThreadedShape
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestStdPort BuilderForestAdmissionPort PV_Src_PortSboxStep

def run (s : State) : Result (State × Unit) := do
  let first ← PV_Src_ExternalReference.run s
  let (a,t,r,i) ← poseidon2.permute_optimized_with_trace_loop0
    (sourceExternalLinear := PV_Src_ExternalReference.dictionary) PV_Src_PortNoop.callback
    ⟨⟨Array.to_slice poseidon2.EXTERNAL_INITIAL,0⟩,0#usize⟩ first () 0#u8 s
  let (b,t1,r1,i1) ← poseidon2.permute_optimized_with_trace_loop1
    PV_Src_PortNoop.callback ⟨poseidon2.INTERNAL.val,0#usize⟩ a t r i
  poseidon2.permute_optimized_with_trace_loop2
    (sourceExternalLinear := PV_Src_ExternalReference.dictionary) PV_Src_PortNoop.callback
    ⟨⟨Array.to_slice poseidon2.EXTERNAL_FINAL,0⟩,0#usize⟩ b t1 r1 i1

theorem source (s : State) :
    poseidon2.permute_optimized_with_trace_threaded
      (sourceExternalLinear := PV_Src_ExternalReference.dictionary) PV_Src_PortNoop.callback s () = run s := by
  rfl

#print axioms source
end R1Z.PV_Src_PortThreadedShape
