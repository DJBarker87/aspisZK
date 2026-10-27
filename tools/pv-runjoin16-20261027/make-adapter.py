from pathlib import Path
import subprocess,json
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
pins=json.loads((R/'evidence/pv-runjoin16-20261027/adapter-source-pins.json').read_text())
def read(name):
 p='docs/research/v8-r0-zk-20261009/lean/R1Z/'+name+'.lean'
 return subprocess.check_output(['git','show',pins[p]['revision']+':'+p],text=True)
ref=read('PV_Src_RecordReference');dirs=read('PV_Src_NativeDirections')
parts=[]
for name,end in [('note','def snapshot'),('snapshot','def witness'),('witness','def publicRecord'),('publicRecord','theorem word_witness')]:
 a=ref.index('def '+name+' (');b=ref.index(end,a);s=ref[a:b]
 s=s.replace('BuilderRecordsReference.Note','S.pool_v1.payment_relation.PoolV1OutputNoteWitnessV1').replace('BuilderRecordsReference.Snapshot','S.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1')
 if name=='witness':s=s.replace('(w : RW)','(w : S.pool_v1.pair_forest_copy_builder.RW)')
 if name=='publicRecord':s=s.replace('(p : RP)','(p : S.pool_v1.pair_forest_copy_builder.RP)')
 parts.append(s)
a=dirs.index('def reference (');b=dirs.index('abbrev closure',a);i=dirs[a:b].replace('def reference (i : Input) : BuilderRecordsPath.Input','def input (i : pair_forest_trace.PoolV1PairForestInputNoteWitnessV1) : S.pool_v1.pair_forest_trace.PoolV1PairForestInputNoteWitnessV1')
s='''import R1Z.PV_RunJoin_RecordsFuns16
import R1Z.PV_RunJoin_ShippedExternal
import R1Z.PV_Src_RecordDynamic
import R1Z.PV_Src_RootHelper
set_option autoImplicit false
namespace R1Z.PV_RunJoin_RecordsAdapter16
open Aeneas Aeneas.Std Result
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
namespace S
export PV_RunJoin_Records (aspis_core)
end S
'''
# A namespace alias is expressed by opening fully qualified names below.
s=s[:s.index('namespace S\n')]
s+='namespace Shipped := PV_RunJoin_Records\n' if False else ''
s+=i+''.join(parts)
s=s.replace('S.pool_v1','PV_RunJoin_Records.pool_v1')
s+='''def R_shipped (empty : Array (Array U32 8#usize) 21#usize) : Records :=
  ⟨fun i out rec chg snap asset => do
    let (w,p) ← PV_RunJoin_Records.pool_v1.pair_forest_copy_builder.records
      (input i) out (rec.map note) (note chg) (snapshot snap) asset empty
    ok (witness w, publicRecord p)⟩

theorem raw_owned_all_words (d : Array U32 8#usize) :
    PV_RunJoin_Records.pool_v1.pair_forest_copy_builder.records.raw_owned d = ok d :=
  BuilderRecordsReference.raw_owned d

#print axioms input
#print axioms note
#print axioms snapshot
#print axioms witness
#print axioms publicRecord
#print axioms R_shipped
#print axioms raw_owned_all_words
end R1Z.PV_RunJoin_RecordsAdapter16
'''
(L/'PV_RunJoin_RecordsAdapter16.lean').write_text(s)
