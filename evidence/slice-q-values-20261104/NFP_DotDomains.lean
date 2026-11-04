import NFP_Carrier
import NFP_HeadDomain
import NFI_WrapperDomains
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFP_DotDomains
open Aeneas Aeneas.Std Result AspisR1Stage2
open NFP_QueryCuts NFP_DotInstall
open Port3_PushFrame

def Canon (x : E) : Prop := NEV_DotCarrier.canonE (FIo_Install.toE x)
/-- Canonical returned dot values are derived from the same NFM execution
and its four original packets; they are not independent successful values. -/
theorem returned (q : Slice U8) (g : Array E 29#usize) (qPlace gPlace : Nat)
 (canonical : NEV_DotInputs.Canonical (FIp_DotsAdapter.toArray g)) (out : Dots)
 (run : dot q g qPlace gPlace = ok out) : ∀ x∈out.val, Canon x := by
 unfold dot at run
 obtain ⟨native,source,equality⟩ := bind_success _ _ _ run
 obtain ⟨window,converted,fixed,a,b,c,d,hw,hc,hf,pa,pb,pc,pd,ha,hb,hcc,hd,shape⟩ :=
  NFI_WrapperDomains.reached NFM_ProductInstance.mainProduct NFM_ProductInstance.main_law
   NFM_ProductInstance.tailProduct NFM_ProductInstance.tail_law q (FIp_DotsAdapter.toArray g)
   qPlace gPlace native canonical source
 have ca := (NFE_NFC_MainPacket.domains pa).2.2.1
 have cb := (NFE_NFC_MainPacket.domains pb).2.2.1
 have cc := (NFE_NFC_MainPacket.domains pc).2.2.1
 have cd := (NFE_NFC_MainPacket.domains pd).2.2.1
 have same := Result.ok.inj equality
 subst out
 intro x member
 change x∈native.val.map FIo_Install.fromE at member
 obtain ⟨value,mem_value,rfl⟩ := List.mem_map.mp member
 unfold Canon
 rw [NFP_Carrier.to_from]
 rw [shape] at mem_value
 simp only [Array.make,List.mem_cons,List.not_mem_nil,or_false] at mem_value
 rcases mem_value with rfl|rfl|rfl|rfl
 · exact ca
 · exact cb
 · exact cc
 · exact cd
#print axioms returned
end AspisR1.NFP_DotDomains
end
