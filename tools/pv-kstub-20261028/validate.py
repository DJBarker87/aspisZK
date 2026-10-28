from pathlib import Path
import json,hashlib,subprocess,re,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-kstub-20261028';errors=[]
def check(b,msg):
 if not b:errors.append(msg)
check(subprocess.check_output(['git','branch','--show-current'],cwd=R,text=True).strip()=='codex/pv-kstub-20261028','branch')
check(str(R)=='/Users/dominic/ZK/.worktrees/pv-relink','worktree')
paths=subprocess.check_output(['git','diff','--name-only','6d4350e42c','HEAD'],cwd=R,text=True).splitlines();check(all(p.startswith(('tools/pv-kstub-20261028/','evidence/pv-kstub-20261028/')) for p in paths),'path-limited commits')
check(hashlib.sha256((E/'KMX_copy_stubs.patch').read_bytes()).hexdigest()=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67','exact patch')
check(all(x.get('original_body_equal',True) for x in json.loads((E/'original-body-bindings.json').read_text())),'historical bodies')
check(all(x['ok'] for x in json.loads((E/'lean-external-preflight.json').read_text())),'external objects')
lean_receipts=sorted(E.glob('447[0-9][0-9]/receipt.json'))
check(len(lean_receipts)<=10,'Lean budget')
for n in [p.parent.name for p in lean_receipts]:
 r=json.loads((E/n/'receipt.json').read_text());check(r['swap']=='0','Lean swap '+n)
 if r['exit']!=0:
  correction=json.loads((E/'lean-parser-correction.json').read_text())
  replacement=E/str(correction['replacement_attempt'])/'receipt.json'
  check(n==str(correction['failed_attempt']) and replacement.exists(),'documented corrected Lean failure '+n)
  if replacement.exists():
   rr=json.loads(replacement.read_text());check(rr['exit']==0 and rr['sha256']==correction['source_after_sha256'] and r['sha256']==correction['source_before_sha256'],'changed-source replacement '+n)
  continue
 log=(E/n/'output.log').read_text();check('sorryAx' not in log and ('axioms:' in log or 'does not depend on any axioms' in log),'axioms '+n)
 for names in re.findall(r'depends on axioms: \[([^\]]*)\]',log):
  check(set(x.strip() for x in names.replace('\n',' ').split(',') if x.strip()) <= {'propext','Classical.choice','Quot.sound'},'standard axioms '+n)
receipts=list(E.glob('K[0-9][0-9]/receipt.json'));check(len(receipts)<=30,'Kani budget')
for f in receipts:
 name=f.parent.name;r=json.loads(f.read_text());target=r['target'];limits=r['limits'];check(limits==dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64),'caps '+name)
 if name=='K01':continue
 check('--exact' in target,'exact selector '+name);check('--unwinding-assertions' in target,'unwinding '+name);check('0-3' in target,'CPU '+name)
 log=(f.parent/'output.log').read_text();check(len(re.findall(r'Checking harness ',log))==1,'one root '+name)
subprocess.run([sys.executable,str(R/'tools/pv-kstub-20261028/audit-controls.py')],check=True)
control_audit={x['run']:x for x in json.loads((E/'control-source-audit.json').read_text())}
for row in json.loads((E/'table.json').read_text())['rows']:
 for h in row['harnesses']:
  if h['confirmed']:
   neg=h['negative_control'];log=(R/neg['receipt']).parent.joinpath('output.log').read_text()
   failures=re.findall(r'^Failed Checks: (.+)$',log,re.M)
   audit=control_audit.get(neg['run'],{})
   check(bool(failures) and audit.get('source_delta_verified') and audit.get('same_bound_and_exact_kmx_stubs'),'intended negative assertion '+h['harness'])
   check(bool(re.search(r'\*\*\s*1 of \d+ failed',log)),'only intended failure '+h['harness'])
 check(row['status']!='pending','unfinished '+row['row'])
for x in json.loads((E/'comparison-inputs.json').read_text()):
 check(hashlib.sha256((R/x['structural_binding']).read_bytes()).hexdigest()==x['binding_sha256'],'structural binding '+x['row'])
for x in json.loads((E/'per-run-kmx-audit.json').read_text())['runs']:
 check(hashlib.sha256((R/x['path']).read_bytes()).hexdigest()==x['stub_sha256'],'exact per-run stub '+x['run'])
check(not any(p.stat().st_size>20*1024*1024 for p in E.rglob('*') if p.is_file()),'file-size cap')
check(not json.loads((E/'observer-pattern-audit.json').read_text())['matching_harnesses'],'observer pattern review')
result=dict(ok=not errors,errors=errors,kani_runs=len(receipts),lean_attempts=len(lean_receipts),paths=paths)
(E/'validation.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='paths'},indent=2));sys.exit(bool(errors))
