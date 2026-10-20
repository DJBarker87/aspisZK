"""Verify current-source receipts and pins without rerunning Lean."""
from pathlib import Path
import hashlib,json,re,subprocess
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]; REPO=ROOT.parents[2]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
subprocess.run(['python3',str(HERE/'generate_adapter.py'),'--check'],check=True,stdout=subprocess.DEVNULL)
freeze=json.loads((ROOT/'evidence/freeze-20261020/source-hashes.json').read_text())
pins={p:{'expected_sha256':h,'actual_sha256':sha(REPO/p)} for p,h in freeze['files'].items()}
assert all(p['expected_sha256']==p['actual_sha256'] for p in pins.values())
(HERE/'source-pins.json').write_text(json.dumps({'freeze_revision':freeze['source_revision'],'checked_revision':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'files':pins,'llbc_comparison':json.loads((ROOT/'evidence/freeze-20261020/llbc-comparison.json').read_text())},indent=2)+'\n')
modules=['Stage2FinishBody','Stage2FinishControl','Stage2QueryChecks','Stage2AccumulatorStep','Stage2FinishPairing','Stage2FirstMatch','Stage2FinishAccumulator','Stage2FinishGeometry','Stage2FinishReducer','Stage2FinishSourceFacts','Stage2FinishChecks','Stage2FinishAudit']
receipts=[json.loads(p.read_text()) for p in HERE.glob('*/receipt.json')]
standard={'propext','Classical.choice','Quot.sound'}
accepted=[]
for module in modules:
 current=sha(ROOT/'lean'/f'{module}.lean')
 candidates=[r for r in receipts if r['module']==module and r['exit']==0 and r['source_sha256']==current]
 assert candidates, f'No current-source accepted receipt: {module}'
 r=max(candidates,key=lambda r:(HERE/r['attempt']/'receipt.json').stat().st_mtime)
 for dep,data in r['imports'].items():
  assert not data.get('missing'), (module,dep)
  assert sha(Path(data['path']))==data['sha256'],(module,dep,'dependency changed; rebuild needed')
 output=(HERE/r['attempt']/'stdout.log').read_text()
 assert not re.search(r'error:|error\(',output),module
 reports=re.findall(r"'([^']+)' (depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)",output,re.S)
 for name,_,axioms in reports:
  assert {s.strip() for s in axioms.split(',') if s.strip()}<=standard,(name,axioms)
 r['audit_names']=[row[0] for row in reports]
 accepted.append({k:r[k] for k in ['module','attempt','source_revision','source_sha256','exit','wall_seconds','peak_rss_bytes','swaps','audit_names']})
# Ensure the focused audit includes every newly declared theorem.
names=[]
for module in modules:
 text=(ROOT/'lean'/f'{module}.lean').read_text()
 names += re.findall(r'^theorem\s+(\w+)',text,re.M)
audit=set(accepted[-1]['audit_names'])
assert all(any(x.endswith('.'+name) for x in audit) for name in names)
summary={'schema':'focused-extractor-proof-packet-v1','scope':'Focused inherited-cache proof packet; not a fresh frozen manifest replay','frozen_inputs_checked':len(pins),'new_theorems':len(names),'accepted':accepted,'maximum_peak_rss_bytes':max(r['peak_rss_bytes'] for r in accepted),'swaps':sum(r['swaps'] for r in accepted),'excluded_attempts':[{'module':r['module'],'attempt':r['attempt'],'exit':r['exit'],'source_sha256':r['source_sha256']} for r in receipts if r['attempt'] not in {x['attempt'] for x in accepted}]}
(HERE/'accepted-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
(HERE/'manifest.json').write_text(json.dumps({'schema':'focused-extractor-proof-packet-v1','attempts':receipts},indent=2)+'\n')
print(json.dumps({k:summary[k] for k in ['frozen_inputs_checked','new_theorems','maximum_peak_rss_bytes','swaps']}))
