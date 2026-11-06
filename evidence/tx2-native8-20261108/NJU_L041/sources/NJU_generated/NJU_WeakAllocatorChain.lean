import NIT_AllocatorChain
import NJU_WeakPairDomain
import NJU_WeakRegularChain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJU_WeakAllocatorChain
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_PairControl
open NIT_AllocatorChain

/- Generalized domain only. Original data/trace/evaluator definitions reused. -/
theorem interpreted (r : NP6_StdModel.Reservation) (c : Context) (out : Result NR)
 (domain : NJU_WeakPairDomain.Domain c.w.value c.alpha.value c.f.value c.kappa)
 (trace : Trace c r out) : letI:=FIo_Install.allocation r
 run c=out := by
 cases trace with
 | rejected e =>
  letI:=FIo_Install.allocation (.Err e)
  rw [run,NHI_FilledModel.qm]
  rfl
 | returned out tail =>
  letI:=FIo_Install.allocation (.Ok ())
  rw [run,NHI_FilledModel.qm]
  change regular c (NHI_FilledModel.vector 64#usize NHX_FilledZero.zeroQ)=out
  exact NJU_WeakRegularChain.interpreted c _ out domain tail


theorem complete (r : NP6_StdModel.Reservation) (c : Context)
 (domain : NJU_WeakPairDomain.Domain c.w.value c.alpha.value c.f.value c.kappa)
 (c0 : canonical c.ap0.value) (c1 : canonical c.ap1.value) :
 ∃ out,Trace c r out ∧ (letI:=FIo_Install.allocation r;run c=out) := by
 have traces : ∃ out,Trace c r out := by
  cases r with
  | Err e => exact ⟨ok (.Err .Allocation),.rejected e⟩
  | Ok u =>
   cases u
   letI:=FIo_Install.allocation (.Ok ())
   have filled : FIo_Native.aspis_core.r0.heap.filled FIo_Native.aspis_core.field.QM31.Insts.CoreMarkerCopy
    64#usize NHX_FilledZero.zeroQ=ok (.Ok (NHI_FilledModel.vector 64#usize NHX_FilledZero.zeroQ)) := by
    rw [NHI_FilledModel.qm];rfl
   have inv := NIG_PairFrames.filled (.Ok ()) _ filled
   obtain ⟨out,tail,_⟩ := NJU_WeakRegularChain.complete c _ domain c0 c1 inv
   exact ⟨out,.returned out tail⟩
 obtain ⟨out,trace⟩ := traces
 exact ⟨out,trace,interpreted r c out domain trace⟩


#print axioms interpreted
#print axioms complete
end AspisR1.NJU_WeakAllocatorChain
