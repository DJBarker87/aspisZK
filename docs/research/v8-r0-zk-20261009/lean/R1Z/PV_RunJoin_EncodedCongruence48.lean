import R1Z.PV_RunJoin_EncodedComplete41
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_EncodedCongruence48
open Aeneas Aeneas.Std Result ProverRwFull
abbrev W := aspis_core.field.wide_exact.WideExact
variable [t : ExternalTypes]

theorem loop (left right : ExternalFuns) (hs : left.op51=right.op51)
    (values : Slice W) (out : alloc.vec.Vec U8) (i : Usize) :
    @prover.encoded_slice_loop t left values out i=@prover.encoded_slice_loop t right values out i := by
  unfold prover.encoded_slice_loop
  have body : (fun (p : alloc.vec.Vec U8 × Usize) => @prover.encoded_slice_loop.body t left values p.1 p.2)=
      (fun (p : alloc.vec.Vec U8 × Usize) => @prover.encoded_slice_loop.body t right values p.1 p.2) := by
    funext p
    simp only [prover.encoded_slice_loop.body,aspis_core.field.wide_exact.WideExact.to_le_bytes,hs]
  rw [body]

theorem complete (left right : ExternalFuns) (hs : left.op51=right.op51) (values : Slice W) :
    @prover.encoded_slice t left values=@prover.encoded_slice t right values := by
  simp only [prover.encoded_slice,loop left right hs]
#print axioms loop
#print axioms complete
end R1Z.PV_RunJoin_EncodedCongruence48
