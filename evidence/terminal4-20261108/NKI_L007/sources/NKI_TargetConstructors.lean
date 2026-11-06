import NKI_DigestTargets
import NJB_TagReduce
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKI_TargetConstructors
open Aeneas Aeneas.Std Result
open NJX_DigestCohort (D dc dcells)
open NKI_DigestTargets (Packet)
theorem left (d : D) (hd : dc d) : ∃ p : Packet d false,True := by
 have hc : (dcells d 7).val<2147483647 := hd _ (List.getElem_mem _)
 exact ⟨⟨dcells d 7,rfl,hc,rfl⟩,True.intro⟩
theorem right (d : D) (hd : dc d) : ∃ p : Packet d true,True := by
 have hc : (dcells d 7).val<2147483647 := hd _ (List.getElem_mem _)
 obtain ⟨t,ct,vt,ht⟩ := NJB_TagReduce.add (dcells d 7) NJX_AppendTargets.tweak hc (by decide)
 exact ⟨⟨t,ct,ht,vt⟩,True.intro⟩
#print axioms left
#print axioms right
end AspisR1.NKI_TargetConstructors
end
