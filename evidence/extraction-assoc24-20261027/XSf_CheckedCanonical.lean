import XSf_A3Ports
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers
set_option autoImplicit false
namespace XSf_CheckedCanonical
open AspisR1 AspisR1ClaimPreparedBridge

theorem valid (q : E.Q) (h : XSa_CheckedQ.valid q=true) :
 LPi_FieldValues.canonQ (LPq_ReadPorts.backQ (toClaimQ (cq q))) := by
 simp only [XSa_CheckedQ.valid,Bool.and_eq_true,decide_eq_true_eq] at h
 rcases h with ⟨⟨⟨a,b⟩,c⟩,d⟩
 change (q.c0.a.val<2147483647 ∧ q.c0.b.val<2147483647) ∧
   (q.c1.a.val<2147483647 ∧ q.c1.b.val<2147483647)
 exact ⟨⟨by scalar_tac,by scalar_tac⟩,⟨by scalar_tac,by scalar_tac⟩⟩

theorem array29 (a : Array C.Q 29#usize)
 (reads : ∀ i : Usize, i.val<29 → ∃ q : E.Q,
   Array.index_usize (arr eq a) i=ok q ∧ XSa_CheckedQ.valid q=true) :
 ∀ q ∈ (mapArray toClaimQ a).val, LPi_FieldValues.canonQ (LPq_ReadPorts.backQ q) := by
 intro q hq
 obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hq
 obtain ⟨i,hi,he⟩ := List.getElem_of_mem hx
 have hb : i<29 := by have h := a.property; change a.val.length=29 at h; omega
 let li := XRn_Join_usize i
 have hv : li.val=i := XRy_ClaimSelect.usize_value i (by omega)
 have hl : li.val<29 := by omega
 obtain ⟨raw,hr,hc⟩ := reads li hl
 rw [XRy_ArrayRead.mapped eq a li hl] at hr
 have hs : raw=eq x := by
   have hs := Result.ok.inj hr
   simpa only [hv,he] using hs.symm
 rw [hs] at hc
 have hc' := valid (eq x) hc
 simpa only [cq_eq] using hc'

#print axioms valid
#print axioms array29
end XSf_CheckedCanonical
