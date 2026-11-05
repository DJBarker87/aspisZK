import NIG_LibraLoop
import NHE_FieldCanonical
set_option autoImplicit false
namespace NIG_LibraWindow
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues
open NIG_LibraLoop

theorem canonical (f:Slice U8) (libra:Libra) (j:Usize) (parts out:Cells)
 (small:j.val<4) (hl:∀x∈libra.val,canonE x) (hp:∀x∈parts.val,canonE x)
 (run:window f libra j parts=ok out):∀x∈out.val,canonE x:=by
 unfold window at run
 obtain ⟨before,hb,run⟩:=Port3_PushFrame.bind_success _ _ _ run
 obtain ⟨coefficient,hc,run⟩:=Port3_PushFrame.bind_success _ _ _ run
 obtain ⟨weight,hw,run⟩:=Port3_PushFrame.bind_success _ _ _ run
 obtain ⟨product,hm,run⟩:=Port3_PushFrame.bind_success _ _ _ run
 obtain ⟨after,ha,run⟩:=Port3_PushFrame.bind_success _ _ _ run
 have cb:=NHM_ArrayCanon.read canonE parts 4#usize before hp hb
 have cc:=NHE_FieldCanonical.success f j (by omega) coefficient hc
 have cw:=NHM_ArrayCanon.read canonE libra j weight hl hw
 have cm:=NHX_FieldResults.wide_mul coefficient weight product cc cw hm
 have ca:=NHX_FieldResults.add before product after cb cm ha
 exact NHM_ArrayPreserve.canonical canonE parts out 4#usize after hp ca run

theorem frame (f:Slice U8) (libra:Libra) (j:Usize) (parts out:Cells)
 (run:window f libra j parts=ok out) (i:Nat) (different:i≠4):
 out.val[i]?=parts.val[i]?:=by
 unfold window at run
 obtain ⟨before,hb,run⟩:=Port3_PushFrame.bind_success _ _ _ run
 obtain ⟨coefficient,hc,run⟩:=Port3_PushFrame.bind_success _ _ _ run
 obtain ⟨weight,hw,run⟩:=Port3_PushFrame.bind_success _ _ _ run
 obtain ⟨product,hm,run⟩:=Port3_PushFrame.bind_success _ _ _ run
 obtain ⟨after,ha,run⟩:=Port3_PushFrame.bind_success _ _ _ run
 exact NHM_ArrayPreserve.frame parts out 4#usize after run i different
#print axioms canonical
#print axioms frame
end NIG_LibraWindow
