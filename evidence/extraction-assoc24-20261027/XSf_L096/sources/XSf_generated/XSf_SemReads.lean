import XSf_CheckedCanonical
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers
set_option autoImplicit false
namespace XSf_SemReads
open AspisR1 AspisR1ClaimPreparedBridge

theorem canonical {H : Type} (sem : C.Sem H) (s : Slice U8)
 (reads : ∀ p : Nat, p<5 → ∀ l : Nat, l<29 → ∃ q : E.Q,
   XRy_ClaimSelect.read (es sem) s p l=ok q ∧ XSa_CheckedQ.valid q=true) :
 LPq_ReadPorts.SemCanonical (toClaimSem sem) := by
 constructor
 · intro row hrow
   obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hrow
   apply XSf_CheckedCanonical.array29 r
   intro li hli
   obtain ⟨p,hp,hpr⟩ := List.getElem_of_mem hr
   have hp3 : p<3 := by have h := sem.claims.property; change sem.claims.val.length=3 at h; omega
   let pi := XRn_Join_usize p
   have hpv : pi.val=p := XRy_ClaimSelect.usize_value p (by omega)
   have hpb : pi.val<3 := by omega
   have hlv : XRn_Join_usize li.val=li := UScalar.eq_of_val_eq (XRy_ClaimSelect.usize_value li.val (by omega))
   obtain ⟨q,hq,hc⟩ := reads p (by omega) li.val hli
   unfold XRy_ClaimSelect.read at hq
   rw [if_pos hp3] at hq
   change (do let a ← Array.index_usize (arr (arr eq) sem.claims) pi
              Array.index_usize a (XRn_Join_usize li.val))=ok q at hq
   rw [XRy_ArrayRead.mapped (arr eq) sem.claims pi hpb,bind_tc_ok] at hq
   simp only [hpv,hpr,hlv] at hq
   exact ⟨q,hq,hc⟩
 · constructor
   · apply XSf_CheckedCanonical.array29 sem.extra
     intro i hi
     obtain ⟨q,hq,hc⟩ := reads 3 (by omega) i.val hi
     have he : XRn_Join_usize i.val=i := UScalar.eq_of_val_eq (XRy_ClaimSelect.usize_value i.val (by omega))
     unfold XRy_ClaimSelect.read at hq
     simp only [show ¬3<3 by omega,if_false,if_pos rfl,es,he] at hq
     exact ⟨q,hq,hc⟩
   · apply XSf_CheckedCanonical.array29 sem.before_z1
     intro i hi
     obtain ⟨q,hq,hc⟩ := reads 4 (by omega) i.val hi
     have he : XRn_Join_usize i.val=i := UScalar.eq_of_val_eq (XRy_ClaimSelect.usize_value i.val (by omega))
     unfold XRy_ClaimSelect.read at hq
     simp only [show ¬4<3 by omega,show ¬4=3 by omega,if_false,if_pos rfl,es,he] at hq
     exact ⟨q,hq,hc⟩

#print axioms canonical
end XSf_SemReads
