import R1Z.PV_Src_PortFullRoundModel
import R1Z.PV_Src_PortSboxAgreement
import R1Z.PV_Src_CanonicalFieldEquality
import R0Z.PoseidonCanon

set_option autoImplicit false
namespace R1Z.PV_Src_PortFullRoundCopy
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_Src_PortSboxStep

theorem initial (s c : State) (hs : Canonical s) (hc : Canonical c) :
    PV_Src_PortFullRoundModel.initial s c = R0PoseidonCopy.full_round s c := by
  letI : Fact (Nat.Prime 2147483647) := ⟨R0Z.m31_prime⟩
  obtain ⟨a,ha,hca,hfa⟩ := PV_Src_PortFullRoundModel.initial_model (K := ZMod 2147483647) s c hs hc
  obtain ⟨b,hb,hfb⟩ := full_round_lift (K := ZMod 2147483647) s c
  have hcb : Canonical b := by
    rw [R0PoseidonCopy.full_round] at hb
    obtain ⟨x,hx,he⟩ := bind_ok_inv hb
    exact fun j => external_canon x b he j.val j.isLt
  have hab := PV_Src_CanonicalFieldEquality.state a b hca hcb
    (fun j => (hfa j).trans (hfb j).symm)
  rw [ha,hb,hab]

theorem final_round (s c : State) (hs : Canonical s) (hc : Canonical c) :
    PV_Src_PortFullRoundModel.final_round s c = R0PoseidonCopy.full_round s c := by
  unfold PV_Src_PortFullRoundModel.final_round
  rw [← PV_Src_PortSboxAgreement.source s c hs hc]
  exact initial s c hs hc

#print axioms initial
#print axioms final_round
end R1Z.PV_Src_PortFullRoundCopy
