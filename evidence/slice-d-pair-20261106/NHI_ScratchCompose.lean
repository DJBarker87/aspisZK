import NHI_ScratchDomain
set_option autoImplicit false
noncomputable section
namespace NHI_ScratchCompose
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues NP6_StdModel
abbrev W := FIo_Native.weights.Weights
abbrev Error := FIo_Native.aspis_core.r0.Error

def run (reservation : Reservation) (w : W) (k : Usize) :
 Result (core.result.Result (Slice NQ) Error) :=
 letI := FIo_Install.allocation reservation
 do
  let r ← FIo_Native.aspis_core.r0.heap.filled FIo_Native.aspis_core.field.QM31.Insts.CoreMarkerCopy
   64#usize NHI_ScratchDomain.zero
  match r with
  | .Err e => ok (.Err e)
  | .Ok v => do
   let out ← FIo_Native.weights.Weights.tensor w k 2#usize v.deref
   ok (.Ok out)

def expected (reservation : Reservation) (w : W) (k : Usize) (hk : k.val<5) :
 Result (core.result.Result (Slice NQ) Error) :=
 match reservation with
 | .Err _ => ok (.Err .Allocation)
 | .Ok () => ok (.Ok (NHI_Tensor.reference w k hk
   (NHI_FilledModel.vector 64#usize NHI_ScratchDomain.zero).deref))

/-- Model-side allocation-to-tensor composition on the SAME scratch vector.
This does not qualify the still-open native filled allocation/frame packet. -/
theorem cohort (reservation : Reservation) (w : W) (k : Usize) (hk : k.val<5)
 (hf : NHI_Tensor.Domain w k hk) : run reservation w k=expected reservation w k hk := by
 cases reservation with
 | Err e =>
  unfold run
  rw [NHI_ScratchDomain.initialized]
  simp only [NHI_FilledModel.result,bind_tc_ok,expected]
 | Ok u =>
  cases u
  unfold run
  rw [NHI_ScratchDomain.initialized]
  simp only [NHI_FilledModel.result,bind_tc_ok]
  have tensor := NHI_Tensor.cohort w k hk hf
   (NHI_FilledModel.vector 64#usize NHI_ScratchDomain.zero).deref
   NHI_ScratchDomain.domain.1 NHI_ScratchDomain.domain.2
  rw [tensor.1,bind_tc_ok]
  rfl

#print axioms cohort
end NHI_ScratchCompose
end
