import NNG_ReferenceHead094
import NNG_ProducerFull094
import NNG_ParseTail094
import NNG_KGuard094
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Candidate094
open Aeneas Aeneas.Std Result NMT_tx1 NMT_CallTree NNG_Observed136

/-- Complete TX1:094 at the installed concrete library and fresh emitted
producer. Its only input clauses are exactly revision4's original Domain. -/
theorem candidate : RSL.TX1_094.RowSpec_094 LIB_Instances.VL LIB_Instances.P NNG_ProducerFull094.producer := by
 intro a obs env own
 rw [NNG_ReferenceHead094.reference a obs env,NNG_ProducerFull094.tree,NNG_ReferenceHead094.port]
 by_cases split : a.k=10
 · have good : (a.k != RSL.SPLIT)=false := by simp [split,RSL.SPLIT]
   have nativeGood : ((NNG_Input094.input a obs env).k != compact.SPLIT)=false := by
    unfold compact.SPLIT
    change (LIBC_Usize.raw a.k !=10#usize)=false
    rw [NNG_KGuard094.guard,good]
   rw [good,RSL.RE.check_false,RSL.RE.seq_pure]
   unfold NNG_PrepareTree094.f_guard
   simp only [nativeGood,Bool.false_eq_true,if_false]
   exact NNG_ParseTail094.source a obs env own split
 · have bad : (a.k != RSL.SPLIT)=true := by simp [split,RSL.SPLIT]
   have nativeBad : ((NNG_Input094.input a obs env).k != compact.SPLIT)=true := by
    unfold compact.SPLIT
    change (LIBC_Usize.raw a.k !=10#usize)=true
    rw [NNG_KGuard094.guard,bad]
   rw [bad,RSL.RE.check_true,RSL.RE.seq_throw]
   unfold NNG_PrepareTree094.f_guard
   simp only [nativeBad,if_true]
   rfl
#check candidate
#print axioms candidate
end AspisR1.NNG_Candidate094
