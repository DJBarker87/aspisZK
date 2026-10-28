import R1Z.PV_CBL_WrapperReference
import R1Z.PV_DL_Truncation
open Aeneas Aeneas.Std Result
namespace R1Z.PV_DL_Forwarding
open PV_CBL_LibraryShapes
set_option autoImplicit false

/-- The core function is a parameter. Only the consumed wrapper is discarded;
the produced output is returned without reinitialization. Native Drop remains
a separate association obligation. -/
theorem output {T A Out : Type}
    (finish : T → Buffer A → Out → Result (T × Buffer A × Out))
    (self : Wrapper T A) (initial produced : Out) (core : T) (buffer : Buffer A)
    (h : finish self.core self.buffer initial=ok (core,buffer,produced)) :
    PV_CBL_WrapperReference.finalize finish self initial=ok produced := by
  simp only [PV_CBL_WrapperReference.finalize,h,bind_tc_ok]
  rfl

theorem failure {T A Out : Type}
    (finish : T → Buffer A → Out → Result (T × Buffer A × Out))
    (self : Wrapper T A) (initial : Out) (e : Error)
    (h : finish self.core self.buffer initial=fail e) :
    PV_CBL_WrapperReference.finalize finish self initial=fail e := by
  simp only [PV_CBL_WrapperReference.finalize,h,bind_tc_fail]

/-- Both changed state and changed buffer are preserved by Ct forwarding;
output truncation is applied only after the variable core returns. -/
def ct {S B : Type} (finish : S → B → Result (S × B × List U8))
    (side : ProverRwFull.digest.core_api.TruncSide) (n : Nat) (state : S) (buffer : B) :
    Result (S × B × List U8) := do
  let (state,buffer,full) ← finish state buffer
  ok (state,buffer,PV_DL_Truncation.value side n full)

theorem ct_restoration {S B : Type} (finish : S → B → Result (S × B × List U8))
    (side : ProverRwFull.digest.core_api.TruncSide) (n : Nat)
    (state changed : S) (buffer restored : B) (full : List U8)
    (h : finish state buffer=ok (changed,restored,full)) :
    ct finish side n state buffer=ok (changed,restored,PV_DL_Truncation.value side n full) := by
  simp only [ct,h,bind_tc_ok]
  rfl

theorem ct_length {S B : Type} (finish : S → B → Result (S × B × List U8))
    (side : ProverRwFull.digest.core_api.TruncSide) (n : Nat)
    (state changed : S) (buffer restored : B) (full : List U8)
    (h : finish state buffer=ok (changed,restored,full)) (hn : n≤full.length) :
    ∃ out, ct finish side n state buffer=ok (changed,restored,out) ∧ out.length=n :=
  ⟨_,ct_restoration finish side n state changed buffer restored full h,
    PV_DL_Truncation.length side n full hn⟩

#print axioms output
#print axioms failure
#print axioms ct
#print axioms ct_restoration
#print axioms ct_length
end R1Z.PV_DL_Forwarding
