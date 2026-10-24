#!/usr/bin/env python3
"""Focused source/dependency audit only. Does not invoke Lean or rewrite historical evidence."""
from pathlib import Path
import hashlib,json,subprocess,re
R=Path(__file__).resolve().parents[2];E=R/'evidence/port18validate-20261024';H=R/'evidence/port18coherence-20261024';L=R/'docs/research/100bit-spend-path-20261013/lean'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
receipts=[json.loads(p.read_text()) for p in sorted(E.glob('lean-*/receipt.json'))]
assert len(receipts)==8 and all(r['kind']=='lean' for r in receipts)
accepted={r['target']:r for r in receipts if r['accepted']}
assert len(accepted)==6
for target,r in accepted.items():
 assert r['exit_status']==0 and r['swaps']==0
 for f,h in r['source_hashes'].items():assert sha(L/f)==h
 for n,d in r['deps_fingerprint']['objects'].items():assert sha(d['path'])==d['sha256'],(target,n)
 obj=Path('/tmp/port18coherence-local-objects')/(target+'.olean');assert sha(obj)==r['object_sha256']
for r in receipts:
 for f,h in r['source_hashes'].items():assert sha(E/r['attempt']/'sources'/f)==h
old=subprocess.check_output(['git','show','1e2b6fe7e9439687bb60ea4a26e3b6b3c094d46b:docs/research/100bit-spend-path-20261013/lean/Port18COHERENCE_Kernel.lean'],cwd=R)
assert (L/'Port18COHERENCE_Kernel.lean').read_bytes().split(b'import Lean',1)[1]==old.split(b'import Lean',1)[1]
# Complete prior positive statements/17 standard-axiom reports retained as historical evidence only.
audit=H/'lean-028/receipt.json';a=json.loads(audit.read_text());assert len(a['print_axioms'])==17
for line in a['print_axioms']:
 m=re.search(r'\[([^]]*)\]',line)
 assert m and set(m[1].replace(' ','').split(','))<={'propext','Classical.choice','Quot.sound'}
probe=(E/'lean-004/stdout.log').read_text()
assert probe.count('REJECTED ')==7 and 'ACCEPTED exact valid' in probe
snap=Path('/tmp/port18coherence-snapshot-manifest.json');s=json.loads(snap.read_text())
assert sha('/tmp/port18coherence-snapshots.tsv')==s['tsv_sha256']
for entry in s['snapshots']:assert sha(entry['path'])==entry['sha256']
changed=subprocess.check_output(['git','diff','--name-only','1e2b6fe7e9439687bb60ea4a26e3b6b3c094d46b'],cwd=R,text=True).splitlines()
assert all('/Port18VALIDATE_' in p or p.endswith('/Port18COHERENCE_Kernel.lean') or p.startswith(('evidence/port18validate-20261024/','tools/port18validate-20261024/')) for p in changed)
for p in E.rglob('*'):
 if p.is_file():assert p.stat().st_size<5000000,p
out={'schema':'focused-extractor-proof-packet-v1','source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),'new_charged':8,'new_actual_lean':8,'new_pre_lean':0,'cumulative_charged':312,'cumulative_actual_lean':307,'cumulative_pre_lean':5,'ceiling':356,'remaining':44,'continuation_allowance_used':'8/8','kani':'0/20 unchanged','accepted_targets':{n:r['attempt'] for n,r in accepted.items()},'receipts':receipts,'snapshot_manifest':{'sha256':sha(snap),'bytes':snap.stat().st_size},'reused_audit':{'receipt':str(audit.relative_to(R)),'sha256':sha(audit),'stdout_sha256':sha(H/'lean-028/stdout.log'),'print_axioms':a['print_axioms'],'assessment':'Historical source-identical positive audit; NOT refreshed against final dependency objects'},'kernel_algorithm_unchanged':True,'original_evidence':'Unmodified; Port17 mixed-cache evidence remains WITHHELD','new_validation':'7 rejection assertions and exact positive theorem/consumer reconstruction; four affected checked stages refreshed','status':'Focused source/dependency audit passes; fresh final normal-import/17-axiom audit remains blocked by continuation attempt allowance','next_validation':'One lead-authorized focused Port18COHERENCE_CheckedAudit attempt with changed dependencies; no full frozen replay','limits':'No native/release closure; all residual R/source/SDK/native/release associations retained; both deployed targets not established'}
(E/'manifest.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:out[k] for k in ['status','cumulative_charged','cumulative_actual_lean','remaining','accepted_targets']}))
