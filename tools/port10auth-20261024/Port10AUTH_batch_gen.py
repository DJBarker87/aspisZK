from pathlib import Path
import sys
R=Path(__file__).resolve().parents[2];L=R/'docs/research/100bit-spend-path-20261013/lean'
s=(L/'Port4B_BatchJoin.lean').read_text();s=s[s.index('/-- Accepted native batch0'):s.index('#print axioms compose')]
a=s.index('    (binary occupied sibling');b=s.index('    (proof : Slice U8)',a)
s=s[:a]+'''    (oracle : CheckpointBytes5Inputs.Oracle (VTop_Checkpoint.digest D) hash H)
    (occupied sibling : MultiproofConeP6Callbacks.Parent) (leaf : MultiproofConeP6Batch.Leaf)
    (occupiedGate : MultiproofConeP6Callbacks.ParentGate (MultiproofConePhysicalTransport.rawOracle H) occupied)
    (siblingGate : MultiproofConeP6Callbacks.ParentGate (MultiproofConePhysicalTransport.rawOracle H) sibling)
    (leafGate : MultiproofConeP6Batch.LeafGate H leaf)
'''+s[b:]
s=s.replace('    ∃ log, eval H','    eval H').replace('batch.val initial)=\n      (log,true)', '''batch.val Port4B_BatchJoin.initial)=
      (CheckpointBytes5Inputs.observe (Port9OR_Code.trace (VTop_Checkpoint.digest D) hash
        (Port9OR_Batch.code base (VTop_Checkpoint.digest D) hash proof p folded batch)).1,true)''')
s=s.replace('⟨a0,s0,h0,i0,v0⟩','⟨s0,h0,i0,v0⟩').replace('⟨a1,s1,h1,i1,v1⟩','⟨s1,h1,i1,v1⟩').replace('⟨a2,s2,h2,i2,v2⟩','⟨s2,h2,i2,v2⟩').replace('Port4B_TreeJoin.accepted','Port10AUTH_Tree.accepted')
s=s.replace('    binary occupied sibling leaf p6 proof','    oracle occupied sibling leaf occupiedGate siblingGate leafGate proof').replace('    initial idx1 val1 c0','    Port4B_BatchJoin.initial idx1 val1 c0')
a=s.index('  exact ⟨_,compose')
s=s[:a]+'''  have code0 := (Port9OR_BatchTree.source base (VTop_Checkpoint.digest D) (VTop_Checkpoint.digest D) hash
    proof p.queries (Port3_BatchStage.root0 p) batch 0#usize Port4B_BatchJoin.initial.idx Port4B_BatchJoin.initial.val).trans c0
  have code1 := (Port9OR_BatchTree.source base (VTop_Checkpoint.digest D) (VTop_Checkpoint.digest D) hash
    proof p.queries (Port3_BatchStage.root1 p) batch 1#usize idx1 val1).trans c1
  have code2 := (Port9OR_BatchTree.source base (VTop_Checkpoint.digest D) (VTop_Checkpoint.digest D) hash
    proof p.queries folded batch 2#usize idx2 val2).trans c2
  have log1 := congrArg₂ (fun idx val => Port9OR_BatchTree.code base (VTop_Checkpoint.digest D) hash
    proof p.queries (Port3_BatchStage.root1 p) batch 1#usize idx val) i0 v0
  have log2 := congrArg₂ (fun idx val => Port9OR_BatchTree.code base (VTop_Checkpoint.digest D) hash
    proof p.queries folded batch 2#usize idx val) i1 v1
  have h1' := h1.trans (congrArg (fun code =>
    (CheckpointBytes5Inputs.observe (Port9OR_Code.trace (VTop_Checkpoint.digest D) hash code).1,(true,s1))) log1)
  have h2' := h2.trans (congrArg (fun code =>
    (CheckpointBytes5Inputs.observe (Port9OR_Code.trace (VTop_Checkpoint.digest D) hash code).1,(true,s2))) log2)
  have combined := Port4B_BatchJoin.compose H occupied sibling leaf parsed q nodes batch.val s0 s1 s2 _ _ _ h0 h1' h2'
  have logs := Port10AUTH_BatchLog.logs base (VTop_Checkpoint.digest D) hash proof p folded batch idx1 idx2 idx3 val1 val2 val3
    code0 code1 code2
  have observed := congrArg CheckpointBytes5Inputs.observe logs
  simp only [CheckpointBytes5Inputs.observe,List.map_append] at observed
  exact combined.trans (congrArg (fun log => (log,true)) observed.symm)
'''
header='''import Port10AUTH_BatchLog

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port10AUTH_Batch
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open MultiproofConeCanonical
'''
out=header+s+'\n#print axioms accepted\nend AspisR1.Port10AUTH_Batch\nend\n';p=L/'Port10AUTH_Batch.lean'
if '--check' in sys.argv:assert p.read_text()==out
else:p.write_text(out)
