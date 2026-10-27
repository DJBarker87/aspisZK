import XSa_PowersList
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XRn_Join_FieldExternal
set_option autoImplicit false
namespace XSa_PowersArray
open AspisR1ClaimPreparedBridge

theorem powers (N : Usize) (x : C.E) (hx : XRy_WideMultiply.Canonical x) :
 ∃ out, XRn_Join_Release.weights.powers N x=ok out ∧
 XRn_Join_powers x N.val XRy_Powers.one=ok out.val ∧ XRy_ClaimFold.canonicalList out.val ∧
 AspisR1CurrentPreparedClaim.ClaimPowers.powers N (toClaimE x)=ok (arr toClaimE out) := by
 obtain ⟨out,pending,xs,hr,hpend,ex,hval⟩ := XSa_PowersList.paired N.val x hx
   (Array.repeat N XRy_Powers.zero) XRy_Powers.one XRy_Powers.one_canonical 0#usize (by scalar_tac)
 have hv : out.val=xs := by simpa only [show (0#usize).val=0 by scalar_tac,List.take_zero,List.nil_append] using hval
 have hpow : XRn_Join_Release.weights.powers N x=ok out := by
   unfold XRn_Join_Release.weights.powers
   simp only [_root_.aspis_core.field.wide_exact.WideExact.ZERO,
     _root_.aspis_core.field.wide_exact.WideExact.ONE,bind_tc_ok]
   change (do let (out,pending) ← XRn_Join_Release.weights.powers_loop x (Array.repeat N XRy_Powers.zero) XRy_Powers.one 0#usize
              match pending with | none => ok out | some out2 => ok out2) = ok out
   rw [hr,bind_tc_ok]
   rcases hpend with h | h <;> rw [h] <;> rfl
 obtain ⟨ys,ey,hylen,hycan⟩ := XRy_ListPowers.total N.val x XRy_Powers.one hx XRy_Powers.one_canonical
 have hxy : xs=ys := Result.ok.inj (ex.symm.trans ey)
 have hpub : powersPublic N x=ok out := (XRy_PowersPublic.powers N x hx).symm.trans hpow
 exact ⟨out,hpow,by simpa only [hv] using ex,by simpa only [hv,hxy] using hycan,
   powersPublic_success x out hpub⟩

#print axioms powers
end XSa_PowersArray
