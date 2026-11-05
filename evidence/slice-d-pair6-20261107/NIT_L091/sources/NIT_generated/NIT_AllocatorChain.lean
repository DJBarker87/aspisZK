import NIT_RegularChain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIT_AllocatorChain
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_PairControl

inductive Trace (c : Context) : NP6_StdModel.Reservation → Result NR → Prop
 | rejected (e : NP6_StdModel.ReserveError) : Trace c (.Err e) (ok (.Err .Allocation))
 | returned (out : Result NR)
   (tail : letI:=FIo_Install.allocation (.Ok ()); NIT_RegularChain.Trace c (NHI_FilledModel.vector 64#usize NHX_FilledZero.zeroQ) out) :
   Trace c (.Ok ()) out

/-- The rejected arm is a complete result, not allocator-success conditioning. -/
theorem interpreted (r : NP6_StdModel.Reservation) (c : Context) (out : Result NR)
 (domain : NIT_PairDomain.Domain c.w.value c.alpha.value c.f.value c.kappa)
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
  exact NIT_RegularChain.interpreted c _ out domain tail

theorem complete (r : NP6_StdModel.Reservation) (c : Context)
 (domain : NIT_PairDomain.Domain c.w.value c.alpha.value c.f.value c.kappa)
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
   obtain ⟨out,tail,_⟩ := NIT_RegularChain.complete c _ domain c0 c1 inv
   exact ⟨out,.returned out tail⟩
 obtain ⟨out,trace⟩ := traces
 exact ⟨out,trace,interpreted r c out domain trace⟩

#print axioms interpreted
#print axioms complete
end AspisR1.NIT_AllocatorChain
