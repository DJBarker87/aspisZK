"""Recover terminal state read-only after the submitted transport reset.
Use stdin for the large source manifest, avoiding a large SSH command argument.
"""
from pathlib import Path
import ast,json,subprocess,shlex,time
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90'
B='/home/dombarker/project-offloads/codex-cx-native-tx2a-20261027'
manifest=json.loads((E/'NBC_SCRATCH_MANIFEST.json').read_text())
modules=json.loads((E/'NBC_TARGETS.json').read_text())['functions']
tree=ast.parse((E/'NBC_finish.py').read_text())
node=next(n.value for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='code' for t in n.targets))
code=eval(compile(ast.Expression(node),'NBC original final source audit','eval'),dict(B=B,manifest=manifest,modules=modules))
code='import sys,json\npayload=json.load(sys.stdin)\n'+code.replace('manifest='+repr(manifest)+';members='+repr(modules),"manifest=payload['manifest'];members=payload['members']")
start=code.index("for name in ['NBC_target','NBC_tmp']:")
end=code.index('print(json.dumps(out))',start)
code=code[:start]+"out['cleanup_observation']={name:(b/name).exists() for name in ['NBC_target','NBC_tmp']}\n"+code[end:]
assert 'rmtree' not in code and len(code)<12000
# Rule10b: wait60, then recover read-only; never resubmit Lean/Kani or cleanup.
time.sleep(60)
for n in range(11):
 r=subprocess.run(['ssh','-o','ConnectTimeout=15',H,'python3 -c '+shlex.quote(code)],input=json.dumps(dict(manifest=manifest,members=modules)),capture_output=True,text=True)
 with (E/'NBC_RECOVERY_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(trial=n,exit=r.returncode,stderr=r.stderr))+'\n')
 if r.returncode==0:break
 if r.returncode==255 and n<10:time.sleep(60);continue
 raise SystemExit(r.stdout+r.stderr)
out=json.loads(r.stdout)
for k,n in [('source','NBC_SOURCE_AUDIT.json'),('cache','NBC_CACHE_END.json'),('aeneas','NBC_LIBRARY_END.json'),('tools','NBC_TOOL_PINS.json')]:
 (E/n).write_text(json.dumps(out[k],indent=2)+'\n')
initial=json.loads((E/'NBC_CACHE_START.json').read_text())
assert all(out['cache'].get(k)==v for k,v in initial.items()),'preexisting persistent object changed'
assert json.loads((E/'NBC_LIBRARY_START.json').read_text())==out['aeneas'],'resolved Aeneas changed'
terminal={k:v for k,v in out.items() if k not in ['source','cache','aeneas','tools']}
terminal.update(initial_cache_files=len(initial),terminal_cache_files=len(out['cache']),all_initial_cache_files_unchanged=True,all_aeneas_pins_unchanged=True)
(E/'NBC_TERMINAL_HOST.json').write_text(json.dumps(terminal,indent=2)+'\n');print(json.dumps(terminal,indent=2))
