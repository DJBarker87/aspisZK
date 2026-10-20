#!/usr/bin/env python3
"""Audit current source, focused receipts, dependency objects and all axioms.
This reads retained evidence only; it never replays an unchanged proof.
"""
import hashlib,json,pathlib,re,subprocess
HERE=pathlib.Path(__file__).resolve().parent
ROOT=HERE.parents[3]; LEAN=HERE.parent/'lean'
modules=['PrivacyR1FinalRelease','BuilderStdModels','BuilderStdShift','BuilderStdCollect','BuilderBankExtracted','BuilderStdArray','BuilderBankShape','BuilderBankArray']
records=[json.loads(x) for x in (HERE/'release-attempts.jsonl').read_text().splitlines()]
last={r['module']:r for r in records}
entries={}
allowed={'propext','Classical.choice','Quot.sound'}
for m in modules:
    r=last['R1Z.'+m];p=LEAN/'R1Z'/f'{m}.lean';s=p.read_text()
    assert r['exit']==0,(m,r['exit'])
    assert hashlib.sha256(p.read_bytes()).hexdigest()==r['source_sha256'],m
    assert not re.search(r'^\s*(?:axiom|opaque)\b|\b(?:sorry|admit|native_decide)\b',s,re.M),m
    for name in re.findall(r'^theorem (\S+)',s,re.M):
        assert '#print axioms '+name in s,(m,name)
    for line in r['axioms']:
        if 'depends on axioms:' in line:
            a={x.strip() for x in line.split('[',1)[1].split(']',1)[0].split(',')}
            assert a<=allowed,(m,a)
    assert r['axioms'],m
    entries['R1Z.'+m]={k:r[k] for k in ['attempt','source_revision','source_dirty','source_sha256','deps_fingerprint','exit','wall','peak_rss_kib','swaps','axioms']}
assert not subprocess.check_output(['git','diff','--name-only','b89c4bae8','--','crates'],cwd=ROOT,text=True).strip(), 'shipped file changed; ELF gate required'
remote='''import pathlib,json,hashlib,re
J=pathlib.Path('/home/dombarker/project-offloads/aspis-joint-20261019')
H=pathlib.Path('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019')
T=pathlib.Path('/home/dombarker/project-offloads/aspis-fs-generic-20261006')
env=json.loads((H/'env/J.json').read_text());roots=[J/'objects']+[pathlib.Path(x) for x in env['LEAN_PATH'].split(':')]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
ans={}
for m,r in ENTRIES.items():
 p=J/'sources'/(m.replace('.','/')+'.lean')
 assert sha(p)==r['source_sha256'],m
 imports=re.findall(r'^import (\\S+)',p.read_text(),re.M)
 deps={};missing={}
 for x in imports:
  obj=x.replace('.','/')+'.olean'
  resolved=next((d/obj for d in roots if (d/obj).exists()),None)
  assert resolved,x
  deps[x]=dict(path=str(resolved),sha256=sha(resolved),size=resolved.stat().st_size)
  jp=J/'objects'/obj
  missing[x]=sha(jp) if jp.exists() else 'missing'
 fp=hashlib.sha256(';'.join(f'{x}={missing[x]}' for x in sorted(imports)).encode()).hexdigest()[:16]
 assert fp==r['deps_fingerprint'],(m,'direct dependencies changed')
 o=J/'objects'/(m.replace('.','/')+'.olean')
 ans[m]=dict(object=dict(path=str(o),sha256=sha(o),size=o.stat().st_size),resolved_imports=deps,
   raw_out_sha256=sha(T/f'evidence/out-{r["attempt"]}.log'),raw_time_sha256=sha(T/f'evidence/time-{r["attempt"]}.log'))
print(json.dumps(dict(modules=ans,env_sha256=sha(H/'env/J.json'),launcher_sha256=sha(pathlib.Path('/home/dombarker/project-offloads/codex-cx-builder-ref5-20261021/run-joint.sh')))))
'''.replace('ENTRIES',repr(entries))
a=json.loads(subprocess.check_output(['ssh','dombarker@100.108.41.90','python3 -'],input=remote,text=True))
for m,r in entries.items():a['modules'][m].update(r)
a.update(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),theorem_count=sum(len(re.findall(r'^theorem ',(LEAN/'R1Z'/f'{m}.lean').read_text(),re.M)) for m in modules),shipped_files_changed=False,runtime_join_inhabited=False,source_checker_retry_join_proved=False,full_frozen_manifest='not replayed; conditional endpoint and isolated new modules only')
(HERE/'release-final-audit.json').write_text(json.dumps(a,indent=2)+'\n')
print('PASS',len(modules),'current modules;',a['theorem_count'],'theorems; standard axioms; unchanged direct dependencies and shipped sources')
