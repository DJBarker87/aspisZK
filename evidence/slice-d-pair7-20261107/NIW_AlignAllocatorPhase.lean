import NIW_AlignRegularPhase
import NIT_AllocatorChain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignAllocatorPhase
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_PairControl

inductive Log where
 | rejected (error : NP6_StdModel.ReserveError)
 | returned (regular : NIW_AlignRegularPhase.Log)

def run (r : NP6_StdModel.Reservation) (c : Context) : Result NR × Log :=
 match r with
 | .Err err => (ok (.Err .Allocation),.rejected err)
 | .Ok _ =>
  letI:=FIo_Install.allocation (.Ok ())
  let regular := NIW_AlignRegularPhase.run c (NHI_FilledModel.vector 64#usize NHX_FilledZero.zeroQ)
  (regular.1,.returned regular.2)

theorem trace (r : NP6_StdModel.Reservation) (c : Context)
 (domain : NIT_PairDomain.Domain c.w.value c.alpha.value c.f.value c.kappa)
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
  exact .returned _ (NIW_AlignRegularPhase.trace c _ domain c0 c1 inv)

theorem source (r : NP6_StdModel.Reservation) (c : Context)
 (domain : NIT_PairDomain.Domain c.w.value c.alpha.value c.f.value c.kappa)
 (c0 : canonical c.ap0.value) (c1 : canonical c.ap1.value) :
 (letI:=FIo_Install.allocation r;NIT_PairControl.run c)=(run r c).1 :=
 NIT_AllocatorChain.interpreted r c _ domain (trace r c domain c0 c1)

#print axioms trace
#print axioms source
end AspisR1.NIW_AlignAllocatorPhase
