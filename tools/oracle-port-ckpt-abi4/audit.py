#!/usr/bin/env python3
"""Audit focused receipts and unchanged frozen sources; no release replay."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
ROOT=Path(__file__).resolve().parents[2]
P=ROOT/'docs/research/100bit-spend-path-20261013'
E=P/'evidence/ckpt-abi4-20261021'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
for script in ['callers.py','remainder.py']:
    subprocess.run(['python3','-B',str(ROOT/'tools/oracle-port-ckpt-abi4'/script),'--check'],check=True)
manifest=json.loads((E/'manifest.json').read_text())
expected={'OraclePortCkptAbi4Interleaved':2,'OraclePortCkptAbi4Std':4,'OraclePortCkptAbi4Decode':4,'OraclePortCkptAbi4Freeze':10}
final=[]
for module,count in expected.items():
    source=P/'lean'/(module+'.lean')
    assert not re.search(r'\b(sorry|admit|native_decide|maxRecDepth|maxHeartbeats)\b|^axiom\s',source.read_text(),re.M)
    rows=[a for a in manifest['attempts'] if a['module']==module and a['final_current']]
    assert len(rows)==1
    a=rows[0]
    assert a['exit']==0 and a['source_sha256']==sha(source)
    assert a['swaps']==0 and a['peak_rss_bytes']<8*1024**3
    assert len(a['axioms'])==count, (module,len(a['axioms']))
    for dependency in a['direct_imports']:
        assert sha(Path(dependency['path']))==dependency['sha256']
    for report in a['axioms']:
        axioms=re.search(r'axioms: \[([\s\S]*?)\]',report)
        if axioms: assert set(re.findall(r'[A-Za-z_.]+',axioms[1])) <= {'propext','Classical.choice','Quot.sound'}
    directory=E/(module+'-'+str(a['attempt']))
    assert sha(directory/'source.lean.txt')==a['source_sha256']
    assert json.loads((directory/'receipt.json').read_text())==a
    log=(directory/'lean.log').read_text()
    assert 'error:' not in log and 'sorryAx' not in log
    final.append({k:a[k] for k in ['module','attempt','source_revision','source_sha256','exit','wall_seconds','peak_rss_bytes','swaps','axioms']})
changed=subprocess.check_output(['git','diff','--name-only','9f42fc11c'],cwd=ROOT,text=True).splitlines()
assert not any(p.startswith(('crates/','programs/')) for p in changed)
for path in changed:
    if '/lean/' in path:
        assert Path(path).name in {m+'.lean' for m in expected}
    assert '/lean-candidates/' not in path
result=dict(schema='checkpoint-abi4-focused-audit-v1',final=final,
 shipped_source_changed=False,elf_rebuild_required=False,full_manifest_replayed=False,
 accepted_run_join=False,headline_premises_removed=0,
 failed_attempts_retained=[dict(module=a['module'],attempt=a['attempt'],exit=a['exit'],errors=a['errors']) for a in manifest['attempts'] if a['exit']!=0])
(E/'audit.json').write_text(json.dumps(result,indent=2)+'\n')
print('Focused evidence passes; checkpoint cone remains open')
