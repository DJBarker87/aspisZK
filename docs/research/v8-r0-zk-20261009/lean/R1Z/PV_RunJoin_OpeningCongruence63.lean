import R1Z.PV_RunJoin_OpeningValues41
import R1Z.PV_RunJoin_EncodedInstalled48
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OpeningCongruence63
open Aeneas Aeneas.Std Result ProverRwFull
abbrev W := aspis_core.field.wide_exact.WideExact
variable [t : ExternalTypes]

theorem baseLoop (left right : ExternalFuns) (hs : left.op51=right.op51)
    (out : alloc.vec.Vec U8) (row : Array W 29#usize) (i : Usize) :
    @prover.append_opening_base_row_loop t left out row i=
      @prover.append_opening_base_row_loop t right out row i := by
  unfold prover.append_opening_base_row_loop
  have body : (fun (p : alloc.vec.Vec U8 × Usize) =>
      @prover.append_opening_base_row_loop.body t left row p.1 p.2)=
    (fun (p : alloc.vec.Vec U8 × Usize) =>
      @prover.append_opening_base_row_loop.body t right row p.1 p.2) := by
    funext p
    simp only [prover.append_opening_base_row_loop.body,
      aspis_core.field.wide_exact.WideExact.to_le_bytes,hs]
  rw [body]

theorem secureLoop (left right : ExternalFuns) (hs : left.op51=right.op51)
    (out : alloc.vec.Vec U8) (row : Array W 29#usize) (i : Usize) :
    @prover.append_opening_secure_row_loop t left out row i=
      @prover.append_opening_secure_row_loop t right out row i := by
  unfold prover.append_opening_secure_row_loop
  have body : (fun (p : alloc.vec.Vec U8 × Usize) =>
      @prover.append_opening_secure_row_loop.body t left row p.1 p.2)=
    (fun (p : alloc.vec.Vec U8 × Usize) =>
      @prover.append_opening_secure_row_loop.body t right row p.1 p.2) := by
    funext p
    simp only [prover.append_opening_secure_row_loop.body,
      aspis_core.field.wide_exact.WideExact.to_le_bytes,hs]
  rw [body]

theorem base (left right : ExternalFuns) (hs : left.op51=right.op51)
    (out : alloc.vec.Vec U8) (row : Array W 29#usize) :
    @prover.append_opening_base_row t left out row=@prover.append_opening_base_row t right out row := by
  simp only [prover.append_opening_base_row,baseLoop left right hs,
    aspis_core.field.wide_exact.WideExact.to_le_bytes,hs]

theorem secure (left right : ExternalFuns) (hs : left.op51=right.op51)
    (out : alloc.vec.Vec U8) (row : Array W 29#usize) :
    @prover.append_opening_secure_row t left out row=@prover.append_opening_secure_row t right out row :=
  secureLoop left right hs out row 26#usize

theorem complete (left right : ExternalFuns) (hs : left.op51=right.op51)
    (out : alloc.vec.Vec U8) (opening : aspis_core.r0.wire.FibreOpening) :
    @prover.append_opening_values t left out opening=@prover.append_opening_values t right out opening := by
  simp only [prover.append_opening_values,base left right hs,secure left right hs]

#print axioms baseLoop
#print axioms secureLoop
#print axioms base
#print axioms secure
#print axioms complete
end R1Z.PV_RunJoin_OpeningCongruence63
