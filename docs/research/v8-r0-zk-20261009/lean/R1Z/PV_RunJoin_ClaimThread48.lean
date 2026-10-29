import R1Z.PV_RunJoin_MergeLoop35
import R1Z.PV_RunJoin_CoefficientInstalled45
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ClaimThread48
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]
abbrev Column := Array aspis_core.field.wide_exact.WideExact 1024#usize

abbrev W := aspis_core.field.wide_exact.WideExact
abbrev Point := aspis_core.r0.domain.Point W

def step (messages : Slice Column) (point : Point) (out : alloc.vec.Vec U8) (lane : Usize) := do
  let a ← Slice.index_usize messages lane
  let value ← aspis_core.r0.encoder.eval_message
    aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField a point
  let wire ← aspis_core.field.wide_exact.WideExact.to_le_bytes value
  alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out (Array.to_slice wire)

def phase (messages : Slice Column) (point : Point) : Nat → alloc.vec.Vec U8 → Usize → Result (alloc.vec.Vec U8)
  | 0,out,_ => .ok out
  | n+1,out,lane => do
    let next ← step messages point out lane
    phase messages point n next (Usize.wrapping_add lane 1#usize)

theorem stop (messages : Slice Column) (point : Point) (out : alloc.vec.Vec U8)
    (lane : Usize) (bound : messages.length ≤ lane.val) :
    prover.opening_claim_bytes_loop.body messages point out lane = .ok (.done out) := by
  simp only [prover.opening_claim_bytes_loop.body,
    show ¬lane < Slice.len messages from (by change ¬lane.val < messages.length;omega),↓reduceIte]

theorem one_step (messages : Slice Column) (point : Point) (out : alloc.vec.Vec U8)
    (lane : Usize) (bound : lane.val < messages.length) :
    prover.opening_claim_bytes_loop.body messages point out lane = (do
      let next ← step messages point out lane
      .ok (.cont (next,Usize.wrapping_add lane 1#usize))) := by
  simp only [prover.opening_claim_bytes_loop.body,
    show lane < Slice.len messages from bound,↓reduceIte,step,lift,bind_assoc_eq,bind_tc_ok]

theorem complete (messages : Slice Column) (point : Point) (out : alloc.vec.Vec U8)
    (lane : Usize) (n : Nat) (small : messages.length ≤ 14336) (bound : lane.val + n = messages.length) :
    prover.opening_claim_bytes_loop messages point out lane = phase messages point n out lane := by
  induction n generalizing out lane with
  | zero =>
    unfold prover.opening_claim_bytes_loop
    rw [ProverRw19LoopBind.loop_bind]
    simp only [stop messages point out lane (by omega),bind_tc_ok,phase]
  | succ n ih =>
    unfold prover.opening_claim_bytes_loop
    rw [ProverRw19LoopBind.loop_bind]
    dsimp only
    rw [one_step messages point out lane (by omega)]
    simp only [bind_assoc_eq,bind_tc_ok,phase]
    apply congrArg (Aeneas.Std.bind (step messages point out lane))
    funext next
    exact ih next _ (by rw [PV_RunJoin_MergeLoop35.increment lane (by omega)];omega)
#print axioms stop
#print axioms one_step
#print axioms complete
end R1Z.PV_RunJoin_ClaimThread48
