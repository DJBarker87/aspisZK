import R1Z.PV_RunJoin_BatchLoopValue44
import R1Z.ProverRwP6ArrayMap
set_option autoImplicit false
namespace R1Z.PV_RunJoin_SourceArray44
open Aeneas Aeneas.Std Result
open ProverCommitWideOps48 ProverCommitMix48 PV_RunJoin_WideArithmetic44

theorem map (n : Usize) (p : Nat → Raw) :
    ProverRwP6ArrayMap.map current (sourceArray n p) = PV_RunJoin_BatchRowValue44.array n p := by
  apply Subtype.ext
  simp only [ProverRwP6ArrayMap.map,sourceArray,PV_RunJoin_BatchRowValue44.array,
    ProverCommitArray49.array,List.map_ofFn]

theorem payload (p : Nat → Raw) (start n : Nat) :
    PV_RunJoin_BatchLoopValue44.payload p start n =
      List.ofFn (fun i : Fin n => current (source (p (start+i.val)))) := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih =>
    rw [PV_RunJoin_BatchLoopValue44.payload,List.ofFn_succ,ih]
    simp only [Fin.val_zero,Nat.add_zero]
    congr 1
    apply congrArg List.ofFn
    funext i
    simp only [Fin.val_succ]
    congr 3
    omega
#print axioms map
#print axioms payload
end R1Z.PV_RunJoin_SourceArray44
