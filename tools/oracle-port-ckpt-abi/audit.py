#!/usr/bin/env python3
"""Read-only proof/receipt audit plus deterministic preservation artifacts."""
from pathlib import Path
import difflib
import hashlib
import json
import re
import subprocess

ROOT=Path(__file__).resolve().parents[2]
PACKET=ROOT/'docs/research/100bit-spend-path-20261013'
HERE=PACKET/'evidence/ckpt-abi-draft-20261021'
BASE='73772c55b'
def sha_bytes(b): return hashlib.sha256(b).hexdigest()
def sha(p): return sha_bytes(Path(p).read_bytes())
def git(*args): return subprocess.check_output(['git',*args],cwd=ROOT)
def put(path,obj): path.write_text(json.dumps(obj,indent=2)+'\n')
manifest=json.loads((HERE/'manifest.json').read_text())
final={}
seen=set()
allowed={'propext','Classical.choice','Quot.sound'}
for a in manifest['attempts']:
    out=HERE/f"{a['module']}-{a['attempt']}"
    key=(a['module'],a['source_sha256'],a['deps_fingerprint'])
    assert key not in seen,('unchanged retry',out)
    seen.add(key)
    assert sha(out/'source.lean.txt')==a['source_sha256'],out
    retained=json.loads((out/'receipt.json').read_text())
    assert {k:v for k,v in retained.items() if k!='final_current'}=={k:v for k,v in a.items() if k!='final_current'},out
    command=json.loads((out/'command.json').read_text())
    for k,v in command.items(): assert a[k]==v,(out,k)
    for k in ['exit','wall_seconds','peak_rss_bytes','swaps','source_revision','deps_fingerprint','axioms','errors']:
        assert k in a,(out,k)
    assert a['argv'][1:4]==['-j1','-M4400','-DElab.async=false']
    assert a['lean_path'].split(':')[0]=='/tmp/codex-cx-ckpt-abi-draft-20261021-objects'
    assert a['swaps']==0
    log=(out/'lean.log').read_text()
    timing=(out/'time.log').read_text()
    assert int(re.search(r'(\d+)\s+maximum resident set size',timing)[1])==a['peak_rss_bytes']
    assert all(line in log for line in a['axioms'])
    if a['final_current']:
        assert a['exit']==0 and not a['errors'],out
        source=PACKET/'lean'/f"{a['module']}.lean"
        assert sha(source)==a['source_sha256'],source
        for item in a['direct_imports']:
            assert sha(item['path'])==item['sha256'],item
        obj=Path(a['argv'][a['argv'].index('-o')+1])
        assert sha(obj)==a['object_sha256'] and obj.stat().st_size==a['object_size']
        for report in a['axioms']:
            if 'depends on axioms:' in report:
                used=set(x.strip() for x in report.split('depends on axioms: [')[1].split(']')[0].replace('\n',' ').split(','))
                assert used<=allowed,(a['module'],used)
        text=source.read_text()
        assert not re.search(r'\b(sorry|admit|native_decide|maxRecDepth|maxHeartbeats)\b',text)
        assert not re.search(r'^\s*axiom\b',text,re.M)
        names=re.findall(r'^(?:private )?theorem\s+(\w+)',text,re.M)
        for name in names:
            assert f'#print axioms {name}' in text,(source,name)
            assert any(re.search(r'\.'+re.escape(name)+r"'",r) for r in a['axioms']),(source,name)
        final[a['module']]={'theorems':len(names),'axiom_reports':len(a['axioms']),
                            'receipt':str((out/'receipt.json').relative_to(ROOT))}
new_modules=list((PACKET/'lean').glob('OraclePortCkptAbi*.lean'))
assert set(final)=={p.stem for p in new_modules}
changes=git('diff','--name-status',BASE).decode().splitlines()
for row in changes:
    kind,path=row.split('\t',1)
    if path.startswith(str((PACKET/'lean').relative_to(ROOT))+'/'):
        assert kind=='A' and Path(path).stem.startswith('OraclePortCkptAbi'),row
    else:
        assert path.startswith(('tools/oracle-port-ckpt-abi/',str(HERE.relative_to(ROOT))+'/')) or path==str((PACKET/'design/CONE-AUDIT-20261021.md').relative_to(ROOT)),row
# Preserve both the requested R19 endpoint and the draft's frozen-model endpoint.
preserved=[]
for name in ['R1FinalSoundnessBinPerQueryR19','OraclePortFrozenOrderHeadline']:
    rel=str((PACKET/'lean'/f'{name}.lean').relative_to(ROOT))
    before=git('show',f'{BASE}:{rel}')
    after=(ROOT/rel).read_bytes()
    diff=''.join(difflib.unified_diff(before.decode().splitlines(True),after.decode().splitlines(True),fromfile=name+'.before',tofile=name+'.after'))
    (HERE/f'{name}-signature.diff').write_text(diff)
    (HERE/f'{name}.before.lean.txt').write_bytes(before)
    (HERE/f'{name}.after.lean.txt').write_bytes(after)
    assert diff=='',name
    preserved.append({'module':name,'before_sha256':sha_bytes(before),'after_sha256':sha_bytes(after),'premise_removals':0})
put(HERE/'signature-preservation.json',preserved)
pins=[]
for rel in [
 'crates/aspis-r1-cost-probe/src/verifier.rs',
 'tools/r22-overflow2-kit/generated/lib.rs',
 'docs/research/100bit-spend-path-20261013/lean/Stage2ContinuationResumeBody.lean',
 'docs/research/100bit-spend-path-20261013/lean/R22Stage2ReaderTotal.lean',
 'docs/research/100bit-spend-path-20261013/lean/OraclePortFrozenOrderDecision.lean',
 'docs/research/100bit-spend-path-20261013/lean/OraclePortCheckpointAbiC5.lean',
 'docs/research/100bit-spend-path-20261013/lean/OraclePortCheckpointResumeC5.lean']:
    data=(ROOT/rel).read_bytes()
    assert git('show',f'{BASE}:{rel}')==data,rel
    pins.append({'path':rel,'sha256':sha_bytes(data),'size':len(data)})
put(HERE/'source-pins.json',pins)
result={'status':'passed; partial cone, no concrete frozen source join',
 'base_revision':git('rev-parse',BASE).decode().strip(),
 'last_compile_revision':manifest['attempts'][-1]['source_revision'],
 'attempts':len(manifest['attempts']),
 'successful_attempts':sum(a['exit']==0 for a in manifest['attempts']),
 'failed_attempts':sum(a['exit']!=0 for a in manifest['attempts']),
 'modules':final,'theorems':sum(m['theorems'] for m in final.values()),
 'final_axiom_reports':sum(m['axiom_reports'] for m in final.values()),
 'peak_rss_bytes':max(a['peak_rss_bytes'] for a in manifest['attempts']),
 'swaps':0,'premise_removals':0,'full_frozen_manifest_replayed':False}
put(HERE/'audit-result.json',result)
print(json.dumps({k:v for k,v in result.items() if k!='modules'},indent=2))
