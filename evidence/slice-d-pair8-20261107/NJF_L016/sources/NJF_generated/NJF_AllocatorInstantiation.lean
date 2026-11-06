import NJF_RegularContinuation
import NIW_AlignAllocatorPhase
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJF_AllocatorInstantiation
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_PairControl

def G (r : NP6_StdModel.Reservation) (c : Context) : Result NR :=
 match r with
 | .Err _ => ok (.Err .Allocation)
 | .Ok _ =>
  letI:=FIo_Install.allocation (.Ok ())
  let before:=NHI_FilledModel.vector 64#usize NHX_FilledZero.zeroQ
  NJF_SharedContinuation.continueWith c
   (NJF_RegularCut.G (NGM_GuardExact.guard c.w.value 2#usize)
    (NJF_RegularInstantiation.instantiate c before)).1

/-- The allocator cut's reply is instantiated with the retained reservation;
its zero64 post establishes regular's invariant internally. -/
theorem source (r : NP6_StdModel.Reservation) (c : Context)
 (domain : NIT_PairDomain.Domain c.w.value c.alpha.value c.f.value c.kappa)
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
  exact NJF_RegularContinuation.source c _ domain c0 c1 (NIG_PairFrames.filled (.Ok ()) _ filled)

#print source
#print axioms source
end AspisR1.NJF_AllocatorInstantiation
