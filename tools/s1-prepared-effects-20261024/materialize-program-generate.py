#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,sys
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';S=B/'lean-candidates/s126-caller-boundary-20261021';E=B/'evidence/s126-current-caller-20261021'
head='''import S1QueryMaterializePairsV1
import S1QueryOverwriteEightV1
set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.PreparedQueryMaterialize
open Aeneas Aeneas.Std Result
open PreparedHashCode
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisV8R19.MemoizedProgramLaw
open AspisS1QueryArrayOperations AspisS1QueryOverwriteEight

def normalMaterialize (state0 : Bytes32) : Program Bytes State (Result (Blocks8 × Blocks8)) :=
'''
normal=''
for i in range(8):
 state='state0' if i==0 else f'(encodeState x{i-1})'
 normal+=f'  .ask (flatten (TranscriptStep.readParts {state} 1#u8)) fun b{i} =>\n'
 normal+=f'  .ask (flatten (TranscriptStep.readParts {state} 2#u8)) fun x{i} =>\n'
normal+='  .done (ok (Array.make 8#usize ['+','.join('encodeState b'+str(i) for i in range(8))+'],\n    Array.make 8#usize ['+','.join('encodeState x'+str(i) for i in range(8))+']))\n'
proof='''
/-- Complete source arrays and ordered oracle program, not just a read set.
Every source array operation is total at its proved fixed index. -/
theorem materialize_program {H : Type} (D : aspis_core.Digest32 H) (hash : H) (state : Bytes32) :
    oracleProgram (materialize effects D hash state)=normalMaterialize state := by
  rw [materialize_code_eq_pairs]
  have mut0 : ∀ a : Blocks8, Array.index_mut_usize a 0#usize=
      ok (a.val[0]'(by have := a.property; simp_all),fun value => a.set 0#usize value) := by
    intro a
    exact index_mut_total a 0#usize (by decide)
  have read0 : ∀ (a : Blocks8) (value : Bytes32), Array.index_usize (a.set 0#usize value) 0#usize=ok value :=
    fun a value => QueryPair.index_set a 0#usize value (by decide)
'''
for i in range(1,8):
 proof+=f'''  have step{i} : ∀ (s : Bytes32) (blocks advances : Blocks8),
      oracleProgram (QueryPair.pairStep D hash s blocks advances {i}#usize)=
        Program.ask (flatten (TranscriptStep.readParts s 1#u8)) (fun b =>
          Program.ask (flatten (TranscriptStep.readParts s 2#u8)) (fun x =>
            .done (ok (encodeState x,blocks.set {i}#usize (encodeState b),advances.set {i}#usize (encodeState x))))) :=
    fun s blocks advances => QueryPair.pairStep_program D hash s blocks advances {i}#usize (by decide)
'''
proof+='''  have overwrite : ∀ (a : Blocks8) (x0 x1 x2 x3 x4 x5 x6 x7 : Bytes32),
      ((((((((a.set 0#usize x0).set 1#usize x1).set 2#usize x2).set 3#usize x3).set
        4#usize x4).set 5#usize x5).set 6#usize x6).set 7#usize x7)=
      Array.make 8#usize [x0,x1,x2,x3,x4,x5,x6,x7] := writeEight_eq_make
  unfold materializePairs normalMaterialize
  simp only [oracleProgram_bind,QueryPair.readState_program,oracleProgram_lift,oracleProgram_pure,
    mut0,read0,'''+','.join('step'+str(i) for i in range(1,8))+''',AspisV8R19.OracleProgramOps.bind,continueOracle,overwrite]

#print axioms materialize_program
end AspisR1PublicPreparation.PreparedQueryMaterialize
'''
out=head+normal+proof;p=S/'S1QueryMaterializeProgramV1.lean';mp=E/'s1-query-materialize-program-source-pins.json';sha=lambda b:hashlib.sha256(b).hexdigest();meta=dict(schema='focused-extractor-proof-packet-v1',candidate_sha256=sha(out.encode()),source=str((S/'S1QueryMaterializePairsV1.lean').relative_to(R)),source_sha256=sha((S/'S1QueryMaterializePairsV1.lean').read_bytes()),asks=16,description='Explicit sixteen-ask normal form with all eight squeeze/advance replies returned in full arrays. Source tuple/setter flow proved by Code equality; each pair uses checked total array laws. No source change or parser reproof.')
if '--check' in sys.argv:assert p.read_text()==out and json.loads(mp.read_text())==meta
else:p.write_text(out);mp.write_text(json.dumps(meta,indent=2)+'\n')
print(json.dumps(dict(asks=16)))
