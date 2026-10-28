import R1Z.PV_RunJoin_MergeLoop35
import R1Z.PV_RunJoin_CoefficientInstalled45
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CoefficientsThread45
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]
abbrev Column := Array aspis_core.field.wide_exact.WideExact 1024#usize

def step (v : transport.Variant) (messages : Slice Column) (out : alloc.vec.Vec Column) (lane : Usize) := do
  let a ← Slice.index_usize messages lane
  let column ← transport.Variant.coefficients aspis_core.field.wide_exact.WideExact.Insts.CoreMarkerCopy v a
  alloc.vec.Vec.push out column

def phase (v : transport.Variant) (messages : Slice Column) : Nat → alloc.vec.Vec Column → Usize → Result (alloc.vec.Vec Column)
  | 0,out,_ => .ok out
  | n+1,out,lane => do
    let next ← step v messages out lane
    phase v messages n next (Usize.wrapping_add lane 1#usize)

theorem stop (v : transport.Variant) (messages : Slice Column) (out : alloc.vec.Vec Column)
    (lane : Usize) (bound : messages.length ≤ lane.val) :
    prover.opening_coefficients_loop.body v messages out lane = .ok (.done out) := by
  simp only [prover.opening_coefficients_loop.body,
    show ¬lane < Slice.len messages from (by change ¬lane.val < messages.length;omega),↓reduceIte]

theorem one_step (v : transport.Variant) (messages : Slice Column) (out : alloc.vec.Vec Column)
    (lane : Usize) (bound : lane.val < messages.length) :
    prover.opening_coefficients_loop.body v messages out lane = (do
      let next ← step v messages out lane
      .ok (.cont (next,Usize.wrapping_add lane 1#usize))) := by
  simp only [prover.opening_coefficients_loop.body,
    show lane < Slice.len messages from bound,↓reduceIte,step,lift,bind_assoc_eq,bind_tc_ok]

theorem complete (v : transport.Variant) (messages : Slice Column) (out : alloc.vec.Vec Column)
    (lane : Usize) (n : Nat) (bound : lane.val + n = messages.length) :
    prover.opening_coefficients_loop v messages out lane = phase v messages n out lane := by
  induction n generalizing out lane with
  | zero =>
    unfold prover.opening_coefficients_loop
    rw [ProverRw19LoopBind.loop_bind]
    simp only [stop v messages out lane (by omega),bind_tc_ok,phase]
  | succ n ih =>
    unfold prover.opening_coefficients_loop
    rw [ProverRw19LoopBind.loop_bind]
    dsimp only
    rw [one_step v messages out lane (by omega)]
    simp only [bind_assoc_eq,bind_tc_ok,phase]
    apply congrArg (Aeneas.Std.bind (step v messages out lane))
    funext next
    exact ih next _ (by rw [PV_RunJoin_MergeLoop35.increment lane (by have h:=messages.property;omega)];omega)
#print axioms stop
#print axioms one_step
#print axioms complete
end R1Z.PV_RunJoin_CoefficientsThread45
