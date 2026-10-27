import R1Z.PV_Src_PortSboxModel
import R1Z.PV_Src_CanonicalFieldEquality

set_option autoImplicit false
namespace R1Z.PV_Src_PortSboxAgreement
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep

theorem source (s c : State) (hs : Canonical s) (hc : Canonical c) :
    poseidon2.permute_optimized_with_trace_loop0_loop0
      {start := 0#usize, «end» := 16#usize} s c =
    poseidon2.permute_optimized_with_trace_loop2_loop0
      {start := 0#usize, «end» := 16#usize} s c := by
  letI : Fact (Nat.Prime 2147483647) := ⟨R0Z.m31_prime⟩
  obtain ⟨a,ha,hca,hfa⟩ := PV_Src_PortSboxModel.initial (K := ZMod 2147483647) s c hs hc
  obtain ⟨b,hb,hcb,hfb⟩ := PV_Src_PortSboxModel.final_round (K := ZMod 2147483647) s c hs hc
  have hab := PV_Src_CanonicalFieldEquality.state a b hca hcb (fun j => (hfa j).trans (hfb j).symm)
  rw [ha,hb,hab]

#print axioms source
end R1Z.PV_Src_PortSboxAgreement
