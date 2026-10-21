#!/usr/bin/env python3
"""Resume the focused copy prototype without rerunning unchanged successes."""
import hashlib, json, pathlib, re, subprocess, sys
ROOT = pathlib.Path(__file__).resolve().parents[2]
E = ROOT/'docs/research/100bit-spend-path-20261013/evidence/import-coll-20261021'
OBJ = pathlib.Path('/tmp/codex-cx-import-coll-20261021-objects')
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
modules = ['ImportUnionNamedDiscriminant'] + [r['module'] for r in json.loads((E/'copy-provenance.json').read_text())] + ['ImportUnionAllConesCx20261021','ImportUnionHeadlineCx20261021']
start = sys.argv[1] if len(sys.argv)>1 else modules[0]
for module in modules[modules.index(start):]:
 source = E/'prototype'/(module.replace('.','/')+'.lean')
 history = [r for r in json.loads((E/'manifest.json').read_text())['attempts'] if r['module']==module]
 previous = history[-1] if history else None
 output = OBJ/(module.replace('.','/')+'.olean')
 if previous and previous['exit']==0 and output.exists() and previous['source_sha256']==sha(source):
  unchanged = True
  for imp in previous['imports']:
   resolved = next((pathlib.Path(d)/(imp['module'].replace('.','/')+'.olean') for d in previous['lean_path'].split(':') if (pathlib.Path(d)/(imp['module'].replace('.','/')+'.olean')).exists()),None)
   if resolved is None or str(resolved)!=imp.get('path') or sha(resolved)!=imp.get('sha256'):
    unchanged = False
  if unchanged:
   print('Reuse unchanged accepted target:',module,flush=True)
   continue
 attempt = str(1+max((int(r['attempt']) for r in history),default=0))
 print('Focused target:', module, 'attempt',attempt,flush=True)
 result = subprocess.run([sys.executable,str(ROOT/'tools/import-union/compile.py'),module,attempt])
 if result.returncode: raise SystemExit(result.returncode)
