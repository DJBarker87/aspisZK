import F3K_SamplerOne
import F3J_SamplerStep
import R1LiteralByteProtocol
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3K_SamplerProtocol
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem exact_run (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (pub : LiteralTranscript.Public) (pf : RawCutProverCompiler.Proof) (row n : Nat) :
    let pr := LiteralByteProtocol.protocol D
    eval H (F3J_SamplerRun.program pf row n (pr.transcript H pub pf row))=
      (((List.range n).map (fun j=>(eval H (pr.chain H pub pf (row+j)).toProgram).1)).flatten,
       pr.transcript H pub pf (row+n)) := by
  let pr := LiteralByteProtocol.protocol D
  induction n generalizing row with
  | zero => simp only [F3J_SamplerRun.program,eval,List.range_zero,List.map_nil,List.flatten_nil,Nat.add_zero]
  | succ n ih =>
    rw [F3J_SamplerStep.step]
    change ((eval H (pr.chain H pub pf row).toProgram).1 ++
      (eval H (F3J_SamplerRun.program pf (row+1) n (pr.transcript H pub pf (row+1)))).1,
      (eval H (F3J_SamplerRun.program pf (row+1) n (pr.transcript H pub pf (row+1)))).2)=_
    rw [ih (row+1)]
    rw [List.range_succ_eq_map]
    simp only [List.map_cons,List.map_map,List.flatten_cons,Function.comp_apply,Nat.add_zero]
    have count : row+1+n=row+(n+1) := by omega
    rw [count]
    congr 2
    apply congrArg List.flatten
    apply List.map_congr_left
    intro j hj
    have index : row+1+j=row+(j+1) := by omega
    rw [index]

theorem initial (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (pub : LiteralTranscript.Public) (pf : RawCutProverCompiler.Proof) (n : Nat) :
    eval H (F3J_SamplerRun.program pf 0 n (FS.emptyPrefix pub))=
      (((List.range n).map (fun j=>(eval H
        ((LiteralByteProtocol.protocol D).chain H pub pf j).toProgram).1)).flatten,
       (LiteralByteProtocol.protocol D).transcript H pub pf n) := by
  simpa only [Nat.zero_add,FS2.Protocol.transcript] using exact_run D H pub pf 0 n

#print axioms exact_run
#print axioms initial
end AspisR1.F3K_SamplerProtocol
end
