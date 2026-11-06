import NKK_RawResult
import NKK_LogAlgebra
import NKK_LogReduce
set_option autoImplicit false
noncomputable section
namespace NKK_RawCps
open Aeneas Aeneas.Std Result NKK_NativeRaw

def cps {T : Type} (n : Usize) : Nat → Reader →
 (List (Array U8 n) → Reader → NJU_Log.Run NJU_ResumeObserved.Event T) →
 NJU_Log.Run NJU_ResumeObserved.Event T
 | 0,r,next => next [] r
 | count+1,r,next => do
   let (b,last) ← NJU_ResumeObserved.recordRaw n r
   cps n count last (fun bs out=>next (b::bs) out)

/-- The SAME raw prefix carries its arbitrary caller continuation, including
all fail/div prefixes; the caller supplies no endpoint equation. -/
theorem source {T : Type} (n : Usize) (count : Nat) (r : Reader)
 (next : List (Array U8 n) → Reader → NJU_Log.Run NJU_ResumeObserved.Event T) :
 (NKK_RawPrefix.literal n count r >>= fun pair=>next pair.1 pair.2)=cps n count r next := by
 induction count generalizing r next with
 | zero => rfl
 | succ count ih =>
  unfold NKK_RawPrefix.literal cps
  rw [NKK_LogAlgebra.bind_assoc]
  apply NKK_LogAlgebra.bind_congr
  rintro ⟨b,last⟩
  rw [NKK_LogAlgebra.bind_assoc]
  simp only [NKK_LogReduce.pure_bind]
  exact ih last (fun bs out=>next (b::bs) out)

#print axioms source
end NKK_RawCps
