#!/usr/bin/env python3
"""Final source-only receipt check. No builds, kernel replay or arithmetic gate."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/port18coherence-20261024';L=R/'docs/research/100bit-spend-path-20261013/lean'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
x=json.loads((E/'manifest.json').read_text());c=json.loads((E/'canonical-manifest.json').read_text());checks=[]
assert x['cumulative_charged']==304 and x['cumulative_actual_lean']==299 and x['cumulative_pre_lean_charges']==5
for stage,attempt in x['accepted_stages'].items():
 r=json.loads((E/attempt/'receipt.json').read_text());assert r['exit_status']==0 and r.get('accepted',True)
 log=(E/attempt/'stdout.log').read_text();assert 'PANIC' not in log and not re.search(r'error(?:\(|:)',log)
 for f,h in r['source_hashes'].items():assert sha(L/f)==h,(stage,f)
 for n,z in r['deps_fingerprint']['objects'].items():assert sha(z['path'])==z['sha256'],(stage,n)
 assert r['swaps']==0
 checks.append({'stage':stage,'attempt':attempt,'receipt_sha256':sha(E/attempt/'receipt.json'),'source_matches_current':True})
audit=json.loads((E/'lean-028/receipt.json').read_text());assert len(audit['print_axioms'])==17
for line in audit['print_axioms']:
 values=set(re.search(r'\[([^]]*)\]',line)[1].replace(' ','').split(','));assert values<={'propext','Classical.choice','Quot.sound'}
assert c['matching_selected_declarations']==15241 and c['fresh_project_declarations']==10375
for f in ['Port18COHERENCE_Kernel.lean','Port18COHERENCE_CompatibilityLoad.lean']:
 found=[json.loads(p.read_text()) for p in E.glob('lean-*/receipt.json') if f in json.loads(p.read_text()).get('source_hashes',{}) and json.loads(p.read_text()).get('exit_status')==0]
 assert found and sha(L/f)==max(found,key=lambda r:r['attempt'])['source_hashes'][f]
for p in E.rglob('*.json'):assert p.stat().st_size<=5000000,str(p)
changed=subprocess.check_output(['git','diff','--name-only','5544611e5fa592c7ca44ab12bf799618d8f773a4','HEAD'],cwd=R,text=True).splitlines()
assert all('/Port18COHERENCE_' in p or p.startswith(('evidence/port18coherence-20261024/','tools/port18coherence-20261024/')) for p in changed),changed
out={'status':'pass: source-only, no new Lean attempt','source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),'checks':checks,'audit_axiom_lines':17,'canonical_manifest_sha256':sha(E/'canonical-manifest.json'),'no_shipped_source_changes':True,'limits':'No claim of full original textual-module replay, IR/native/release identity or zero residual R'}
(E/'source-check.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
