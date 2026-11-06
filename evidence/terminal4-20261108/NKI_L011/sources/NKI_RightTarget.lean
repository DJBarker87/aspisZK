import NKI_DigestTargets
import NKI_TweakScalar
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKI_RightTarget
open Aeneas Aeneas.Std Result
open NJX_DigestCohort (D dc dcells)
open NKI_DigestTargets (Packet)
theorem source (d : D) (hd : dc d) : ∃ p : Packet d true,True := by
 have hc : (dcells d 7).val<2147483647 := hd _ (List.getElem_mem _)
 obtain ⟨t,ct,vt,ht⟩ := NKI_TweakScalar.source (dcells d 7) hc
 have value : t.val=NKI_DigestView.target d true 7 := by
  simp only [NKI_DigestView.target,show (7 : Fin 8).val=7 from rfl,and_self,if_true]
  exact vt
 exact ⟨⟨t,ct,ht,value⟩,True.intro⟩
#print source
#print axioms source
end AspisR1.NKI_RightTarget
end
