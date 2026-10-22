#!/usr/bin/env python3
"""Collect small certificate JSONs and hash every retained analysis output."""
import hashlib,json,shlex,subprocess,sys
from pathlib import Path
R=Path(__file__).resolve().parents[2]
E=R/'docs/research/100bit-spend-path-20261013/evidence/s10-repin-20261022'
H='/home/dombarker/project-offloads/codex-cx-s10-repin-20261022';REMOTE='dombarker@100.108.41.90'
paths=['collected/elf-graphs.json','collected/elf-symbol-kinds.json','elf-raw-input.json','elf-crosscheck.json',
 'packet/frontiers-default.json','packet/frontiers-devnet.json','packet/frontiers-pool.json',
 'packet/llvm-linked-definitions.json','packet/frontier-frozen-bodies.txt','packet/ordering-observations.json',
 'cfg.json','instances.json','indirect.json','resolved.json']
if '--diff' in sys.argv:paths=['mir-diff.json','mono-diff.json','elf-diff.json','mir-declarations.json','llvm-diff.json','mono-exact-diff.json']
code='''
from pathlib import Path
import hashlib,json
H=Path(%r)
rows=[]
for s in %r:
 p=H/s;rows.append(dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
print(json.dumps(rows))
''' % (H,paths)
pins=json.loads(subprocess.check_output(['ssh',REMOTE,'python3 -c '+shlex.quote(code)],text=True))
small=[r for r in pins if r['bytes']<=5_000_000]
subprocess.run(['scp','-q',*[REMOTE+':'+r['path'] for r in small],str(E)+'/'],check=True)
for r in small:
 p=E/Path(r['path']).name;assert hashlib.sha256(p.read_bytes()).hexdigest()==r['sha256']
manifest=dict(schema='s10-adopted-analysis-artifacts-v1',actual_source_revision=json.loads((E/'source-inputs.json').read_text())['source_revision'],
 artifacts=pins,host_only=[r for r in pins if r not in small],
 receipt_revision_correction='capped.py raw receipt source_revision is historical hard-coded b2727acd; actual compiler source is source-inputs.json. Invocation revision identifies analysis tools, not compiler input.',
 print_axioms='N/A: no Lean; retained standard-axiom generic graph mathematics is reused only as mathematics')
(E/('diff-manifest.json' if '--diff' in sys.argv else 'analysis-manifest.json')).write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n')
print(json.dumps(dict(artifacts=len(pins),copied=len(small),host_only=len(pins)-len(small))))
