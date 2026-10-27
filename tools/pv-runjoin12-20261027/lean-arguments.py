"""Emit native fixture argument carriers; no compiled payload is generated."""
from pathlib import Path
import ast,re,json,hashlib,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin12-20261027';out=(E/'pv12-fixture-words-02/out.log').read_text()
vals={name:ast.literal_eval(re.search('^'+name+'=(.*)$',out,re.M)[1]) for name in ['input_commitment','lane_anchor','global_anchor']};inverse=int(re.search(r'^second_occupancy_inverse=(\d+)$',out,re.M)[1])
source=R/'crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal_constants.rs';roots=ast.literal_eval(source.read_text().split(' = ',1)[1].strip().removesuffix(';'))
arr=lambda values,n:'Array.make '+str(n)+'#usize ['+', '.join(str(x)+'#u32' for x in values)+']'
digest=lambda seed:arr([seed+17*i+1 for i in range(8)],8)
a8=lambda values:arr(values,8)
a20=lambda rows:'Array.make 20#usize [\n'+',\n'.join(a8(row) for row in rows)+']'
text='''import R1Z.PV_Src_NativeInput
import R1Z.PV_RunJoin_RecordedTransfer
import R1Z.PV_RunJoin_RecordedWithdrawal

/-! Literal argument carriers from the pinned deterministic native probe.
This file supplies no compilation payload and proves no fixture-generator,
compiler-return, parser, or deployed-selection equation. -/
set_option autoImplicit false
namespace R1Z.PV_RunJoin_FixtureArguments
open Aeneas Aeneas.Std
open BuilderForestAdmissionPort.pool_v1

def witness : pair_forest_trace.PoolV1PairForestInputNoteWitnessV1 where
 pair := {
 nullifier_key := '''+digest(10)+'''
 salt := '''+digest(100)+'''
 value := 1000#u32
 pair_leaf := {
 first_commitment := '''+a8(vals['input_commitment'])+'''
 second_occupied := 1#u32
 second_commitment := '''+digest(900)+f'''
 second_occupancy_inverse := {inverse}#u32 }}
 selected_second := false
 membership := {{
 siblings := '''+a20([[2000+20*l+17*i+1 for i in range(8)] for l in range(20)])+'''
 index := 344865#u32 } }
 super_root_siblings := Array.make 3#usize ['''+', '.join(digest(s) for s in [3000,3100,3200])+''']
 super_root_directions := Array.make 3#usize [true,false,true]

def snapshot : pair_tree_profile.PoolV1PairLiveSnapshotV1 where
 pool := PV_RunJoin_RecordedTransfer.publicRecord.pool
 deployment_domain := PV_RunJoin_RecordedTransfer.publicRecord.deployment_domain
 sequence := 0#u64
 next_pair_index := 0#u64
 current_root := '''+a8(roots[20])+'''
 frontier := '''+a20(roots[:20])+'''

'''
for name,owner,salt,value in [('recipient',300,400,600),('transferChange',500,600,400),('withdrawalChange',700,800,750)]:text+=f'def {name} : payment_relation.PoolV1OutputNoteWitnessV1 :=\n  ⟨{digest(owner)}, {digest(salt)}, {value}#u32⟩\n\n'
text+='def laneAnchor : Array U32 8#usize := '+a8(vals['lane_anchor'])+'\n\n'
text+='''def transferRequest : PV_Src_NativeInput.Request :=
 .transfer PV_RunJoin_RecordedTransfer.publicRecord recipient

def withdrawalRequest : PV_Src_NativeInput.Request :=
 .withdrawal PV_RunJoin_RecordedWithdrawal.publicRecord

#print axioms witness
#print axioms snapshot
#print axioms recipient
#print axioms transferChange
#print axioms withdrawalChange
#print axioms laneAnchor
#print axioms transferRequest
#print axioms withdrawalRequest
end R1Z.PV_RunJoin_FixtureArguments
'''
dst=R/'docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_FixtureArguments.lean'
if '--check' in sys.argv:assert dst.read_text()==text
else:dst.write_text(text)
(E/'lean-arguments-pins.json').write_text(json.dumps(dict(native_receipt='pv12-fixture-words-02/receipt.json',native_stdout_sha256=hashlib.sha256(out.encode()).hexdigest(),root_table_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),generated_source_sha256=hashlib.sha256(text.encode()).hexdigest(),classification='literal native argument data only; no compiled payload or source-generator equation'),indent=2)+'\n')
print('Lean argument generator/check passed')
