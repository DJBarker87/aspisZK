import T2Nat_FinishCode
import SdkC_Source
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3N_FinishLog
open Aeneas Aeneas.Std Result AspisR1Stage2

theorem silent {A : Type} (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (c : T2Nat_Silent.Silent A) (before : SdkC_Source.Log) :
    SdkC_Source.run hashv (T2Nat_Silent.code c) before=(T2Nat_Silent.erase c,before) := by
  induction c with
  | done a => rfl
  | step r next ih =>
    cases r <;> simp only [T2Nat_Silent.code,T2Nat_Silent.erase,SdkC_Source.run,
      bind_tc_ok,bind_tc_fail,bind_tc_div,ih]

theorem parent {W : Type} (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (ops : Port3_NativeFinishBody.Ops W) (v : verifier.View) (p : verifier.Prepared)
    (a : verifier.Accumulator) (obs : Option (verifier.Phase → Result Unit)) :
    SdkC_Source.run hashv (T2Nat_Silent.code (T2Nat_FinishCode.parent ops v p a obs)) []=
      (Port3_NativeFinishBody.verifier.finish_relation ops v p a obs,[]) := by
  rw [silent,T2Nat_FinishCode.parent_erase]

theorem reads {W : Type} (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (ops : Port3_NativeFinishBody.Ops W) (v : verifier.View) (p : verifier.Prepared)
    (a : verifier.Accumulator) (obs : Option (verifier.Phase → Result Unit)) :
    SdkC_Source.readLog (SdkC_Source.run hashv
      (T2Nat_Silent.code (T2Nat_FinishCode.parent ops v p a obs)) []).2=[] := by
  rw [parent]
  rfl

#print axioms silent
#print axioms parent
#print axioms reads
end AspisR1.F3N_FinishLog
end
