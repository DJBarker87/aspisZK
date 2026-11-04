import Lean
import NFN_PhaseTransport
import NFS_NEV_BasisOuterStep

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace NFS_NEV_BasisOuterRaw
open Aeneas Aeneas.Std Result ControlFlow AspisR1 AspisR1Stage2 Port3_NativeQueryBody
open S7Kani3BasisOuter (levels t2 double)
/-- Transport the new emitted outer loop through the retained six-level
schedule. Existing S7 totality supplies intermediate basis/node results. -/
theorem levels_eq (ops : Ops) (fuel : Nat) (basis : Array U32 256#usize)
    (node : U32) (n width : Usize) (positive : 0<n.val) (bound : width.val≤256)
    (schedule : n.val*2^fuel=width.val) :
    NEV_AccumulateRaw.accumulate_batched_with_node_loop0 1#u32 node width basis n=
      verifier.accumulate_batched_with_node_loop0 (NBF_BasisInstall.install ops)
        1#u32 node width basis n := by
  induction fuel generalizing basis node n with
  | zero =>
    have done : ¬n<width := by
      change ¬n.val<width.val
      simp only [pow_zero,Nat.mul_one] at schedule
      omega
    unfold NEV_AccumulateRaw.accumulate_batched_with_node_loop0
      verifier.accumulate_batched_with_node_loop0
    rw [Aeneas.Std.loop.eq_def,Aeneas.Std.loop.eq_def]
    dsimp only
    simp only [NEV_AccumulateRaw.accumulate_batched_with_node_loop0.body,
      verifier.accumulate_batched_with_node_loop0.body,if_neg done,bind_tc_ok]
  | succ k ih =>
    have power : 0<2^k := by positivity
    have doubleBound : n.val*2≤width.val := by
      have : 1≤2^k := by omega
      have := Nat.mul_le_mul_left (n.val*2) this
      rw [pow_succ] at schedule
      nlinarith
    have small : n.val≤128 := by omega
    have active : n<width := by
      change n.val<width.val
      have : 2≤2^(k+1) := by rw [pow_succ];omega
      nlinarith
    let n1 := Usize.wrapping_mul n 2#usize
    have successor : n1.val=n.val*2 := Port3_Wrapping.wrap_mul_value n 2#usize
      (by change n.val*2≤4096;omega)
    have block := NBF_BasisInstall.block ops basis node n small
    have body : verifier.accumulate_batched_with_node_loop0.body
        (NBF_BasisInstall.install ops) 1#u32 width node basis n=
        (do let b1 ← S7Kani2BasisLoop.basis_block_owned
              AspisR1Qm31ArithmeticProbe.field.M31.mul basis node n 0#usize
            let node1 ← t2 node
            ok (cont (node1,b1,n1))) := by
      unfold verifier.accumulate_batched_with_node_loop0.body
      rw [if_pos active,block]
      simp only [NBF_BasisInstall.install,t2,double,lift,bind_tc_ok,bind_assoc_eq]
      rfl
    unfold NEV_AccumulateRaw.accumulate_batched_with_node_loop0
      verifier.accumulate_batched_with_node_loop0
    rw [Aeneas.Std.loop.eq_def,Aeneas.Std.loop.eq_def]
    dsimp only
    rw [NFS_NEV_BasisOuterStep.body ops 1#u32 node width n basis small,body]
    obtain ⟨b1,hb⟩ := S7Kani3BasisTotal.block_total basis node n 0#usize n.val small (by simp)
    obtain ⟨node1,ht,hcanon⟩ := S7Kani3BasisOuter.t2_total node
    simp only [hb,ht,bind_tc_ok]
    exact ih b1 node1 n1 (by rw [successor];omega) (by
      rw [successor]
      rw [pow_succ] at schedule
      nlinarith)

#print axioms levels_eq
end NFS_NEV_BasisOuterRaw
end

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
