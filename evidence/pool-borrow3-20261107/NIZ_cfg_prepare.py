import sys,json,hashlib
from pathlib import Path
sys.dont_write_bytecode=True
from NIZ_native_prepare import stage,attrs
E=Path(__file__).resolve().parent
label,mode=sys.argv[1:]
p=E/'NIZ_CFG_CERTIFICATES.json';data=json.loads(p.read_text());c=next(x for x in data['certificates'] if x['label']==label)
assert not c['intersections']
rows=[];mutated=False
for i,e in enumerate(c['edges']):
 barrier=e['barrier_source']
 if mode=='negative' and barrier and not e['safe_target'] and not mutated:barrier=False;mutated=True
 rows.append(f'{i}=>({str(e["safe_source"]).lower()},{str(e["safe_target"]).lower()},{str(barrier).lower()}),')
assert mode=='positive' or mutated
body='let edge:u16=kani::any();kani::assume(usize::from(edge)<'+str(len(rows))+');let (safe_source,safe_target,barrier)=match edge{'+''.join(rows)+'_=>{kani::assume(false);return;}};assert!(!safe_source||barrier||safe_target);'
source=attrs()+'\n#[kani::proof]\nfn certificate(){'+body+'}\n'
stage('programs/aspis-pool/src/processor.rs',source,'frozen MIR one-edge barrier dominance certificate',mode,'One arbitrary edge of the exact pinned frozen MIR graph; includes normal/error/unwind edges. No runtime inputs or transaction shapes.','This proves CFG barrier visitation only. Candidate counter stores still need SAME-cell/guard identity and returned-Ok branch association; no owner ScopeRun or CPI footprint is supplied.',dict(expected_verdict='FAIL' if mode=='negative' else 'PASS',member=label,native_args=['--unwind','3'],graph_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),barrier=c['barrier'],targets=c['targets'],control='remove uniqueness/planner barrier mark at its actual outgoing edge' if mode=='negative' else None))
