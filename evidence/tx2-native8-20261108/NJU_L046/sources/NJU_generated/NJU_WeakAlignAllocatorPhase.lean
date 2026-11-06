import NIW_AlignAllocatorPhase
import NJU_WeakPairDomain
import NJU_WeakAllocatorChain
import NJU_WeakAlignRegularPhase
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJU_WeakAlignAllocatorPhase
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_PairControl
open NIW_AlignAllocatorPhase

/- Generalized domain only. Original data/trace/evaluator definitions reused. -/
theorem trace (r : NP6_StdModel.Reservation) (c : Context)
 (domain : NJU_WeakPairDomain.Domain c.w.value c.alpha.value c.f.value c.kappa)
 (c0 : canonical c.ap0.value) (c1 : canonical c.ap1.value) :
 NIT_AllocatorChain.Trace c r (run r c).1 := by
 cases r with
 | Err err => exact .rejected err
 | Ok unit =>
  cases unit
  letI:=FIo_Install.allocation (.Ok ())
  have filled : FIo_Native.aspis_core.r0.heap.filled FIo_Native.aspis_core.field.QM31.Insts.CoreMarkerCopy
   64#usize NHX_FilledZero.zeroQ=ok (.Ok (NHI_FilledModel.vector 64#usize NHX_FilledZero.zeroQ)) := by
   rw [NHI_FilledModel.qm];rfl
  have inv := NIG_PairFrames.filled (.Ok ()) _ filled
  exact .returned _ (NJU_WeakAlignRegularPhase.trace c _ domain c0 c1 inv)


theorem source (r : NP6_StdModel.Reservation) (c : Context)
 (domain : NJU_WeakPairDomain.Domain c.w.value c.alpha.value c.f.value c.kappa)
 (c0 : canonical c.ap0.value) (c1 : canonical c.ap1.value) :
 (letI:=FIo_Install.allocation r;NIT_PairControl.run c)=(run r c).1 :=
 NJU_WeakAllocatorChain.interpreted r c _ domain (trace r c domain c0 c1)


#print axioms trace
#print axioms source
end AspisR1.NJU_WeakAlignAllocatorPhase
