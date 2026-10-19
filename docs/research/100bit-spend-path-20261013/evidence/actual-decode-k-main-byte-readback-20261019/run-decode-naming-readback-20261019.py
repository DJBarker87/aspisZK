from pathlib import Path
import json,re,subprocess,time
root=Path('/Users/dominic/ZK/docs/research/100bit-spend-path-20261013/lean/extracted-decode-k-canonicality-20261018')
overlay=Path('/tmp/root-decode-main-named-instance-20261019')
modules={'.'.join(f.relative_to(root).with_suffix('').parts):f for f in root.rglob('*.lean')}
target='AspisR1DecodeKFullSuccessIndexedParser'
seen={'AspisR1DecodeKFullV10.Types','DecodeKOptionDiscriminantBridge'};seen.update(x['module'] for x in json.loads((overlay/'canonicality-closure-progress.json').read_text()));order=[]
def visit(m):
 if m in seen:return
 seen.add(m)
 for dep in re.findall(r'^import (\S+)',modules[m].read_text(),re.M):
  if dep in modules:visit(dep)
 order.append(m)
visit(target)
(overlay/'readback-closure-plan.json').write_text(json.dumps({'target':target,'ordered_targets':order,'reason':'The Types discriminant instance name changed to permit a joint import. Recompile the minimal dependent decoder canonicality closure against the changed Types; retain cached Aeneas/Mathlib and unchanged external dependencies.'},indent=2)+'\n')
results=[]
for i,m in enumerate(order):
 attempt=f'named-decode-readback-{i:02d}-root-20261019'
 cmd=['python3','/tmp/run-local-lean-exclusive-20261019.py',m,str(modules[m]),attempt,'/tmp/run-root-named-decode-main-20261019.py']
 print('START',m,flush=True)
 rc=subprocess.run(cmd).returncode
 results.append({'module':m,'attempt':attempt,'exit_status':rc})
 (overlay/'readback-closure-progress.json').write_text(json.dumps(results,indent=2)+'\n')
 if rc:raise SystemExit(rc)
 print('GREEN',m,flush=True)
print('COMPLETE',target,len(order),flush=True)
