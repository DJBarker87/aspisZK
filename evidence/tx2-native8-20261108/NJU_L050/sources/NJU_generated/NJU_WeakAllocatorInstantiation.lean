import NJF_AllocatorInstantiation
import NJU_WeakPairDomain
import NJU_WeakAlignAllocatorPhase
import NJU_WeakRegularContinuation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJU_WeakAllocatorInstantiation
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_PairControl
open NJF_AllocatorInstantiation

/- Generalized domain only. Original data/trace/evaluator definitions reused. -/
theorem source (r : NP6_StdModel.Reservation) (c : Context)
 (domain : NJU_WeakPairDomain.Domain c.w.value c.alpha.value c.f.value c.kappa)
 (c0 : canonical c.ap0.value) (c1 : canonical c.ap1.value) :
 G r c=(NIW_AlignAllocatorPhase.run r c).1 := by
 cases r with
 | Err err => rfl
 | Ok unit =>
  cases unit
  letI:=FIo_Install.allocation (.Ok ())
  have filled : FIo_Native.aspis_core.r0.heap.filled FIo_Native.aspis_core.field.QM31.Insts.CoreMarkerCopy
   64#usize NHX_FilledZero.zeroQ=ok (.Ok (NHI_FilledModel.vector 64#usize NHX_FilledZero.zeroQ)) := by
   rw [NHI_FilledModel.qm];rfl
  exact NJU_WeakRegularContinuation.source c _ domain c0 c1 (NIG_PairFrames.filled (.Ok ()) _ filled)


#print axioms source
end AspisR1.NJU_WeakAllocatorInstantiation
