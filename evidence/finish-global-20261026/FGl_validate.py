#!/usr/bin/env python3
"""Validate focused proof evidence without invoking a compiler."""
from pathlib import Path
import hashlib,json,re,subprocess
E=Path(__file__).resolve().parent;ROOT=E.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=[];covered={};audits=[];failed=[]
for config in sorted(E.glob('FGl_[0-9][0-9][0-9].json')):
    a=config.stem;d=E/a
    if not (d/'receipt.json').exists():
        assert a=='FGl_081' and (E/'FGl_STOP.json').exists()
        continue
    r=json.loads((d/'receipt.json').read_text());rows.append(r)
    assert r['attempt']==a and len(r['sources'])==1
    assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
    assert '-M7000' in r['command'] and r['swaps']=='0'
    assert r['deps_fingerprint']['selected_objects']
    assert json.loads((E/(a+'-reservation.json')).read_text())['allowed']
    for s in r['sources']:assert sha(d/'sources'/s)==r['source_hashes'][s]
    log=(d/'stdout.log').read_text()
    if r['exit_status']:
        assert r['exit_status']==1
        failed.append(dict(attempt=a,source=r['sources'][0],errors=[l for l in log.splitlines() if 'error' in l]))
        continue
    assert not re.search(r'\berror(?:\(|:)|sorryAx',log)
    for s in r['sources']:
        assert sha(ROOT/'lean'/s)==r['source_hashes'][s],s
        covered[s]=dict(attempt=a,sha256=r['source_hashes'][s])
    for line in r['print_axioms']:
        if 'depends on axioms:' in line:
            assert set(line.split('[',1)[1].split(']',1)[0].split(', '))<={'propext','Classical.choice','Quot.sound'}
        audits.append(dict(attempt=a,line=line))
theorems=[]
for p in sorted((ROOT/'lean').glob('FGl_*.lean')):
    s=p.read_text();assert p.name in covered,('not checked',p.name)
    assert not re.search(r'\b(sorry|admit|native_decide)\b|^\s*axiom\s|set_option\s+(maxRecDepth|maxHeartbeats)',s,re.M)
    for m in re.finditer(r'^theorem (\w+)',s,re.M):
        ns=re.search(r'^namespace ([\w.]+)',s,re.M)[1];full=ns+'.'+m[1]
        aa=[x for x in audits if "'"+full+"'" in x['line']];assert aa,full
        theorems.append(dict(name=full,source=p.name,audits=aa))
# No existing source, candidate, shipped artifact or other prefix changed.
changed=subprocess.check_output(['git','diff','--name-only','810eaab3d2','HEAD'],cwd=ROOT,text=True).splitlines()
for p in changed:assert p.startswith('evidence/finish-global-20261026/') or (p.startswith('lean/FGl_') and p.endswith('.lean')),p
result=dict(lean_attempts=len(rows),passes=len(rows)-len(failed),failures=failed,kani_runs=0,
    budget_exhausted=len(rows)==100,mandatory_infrastructure_stop=json.loads((E/'FGl_STOP.json').read_text()),wall_seconds=sum(r['wall_seconds'] for r in rows),
    peak_rss_kib=max(int(r['peak_rss_kib']) for r in rows),swaps=0,
    checked_modules=len(covered),new_theorems=len(theorems),
    source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
    scope='Focused FGl closure over pinned coherent SInt2/F3Y/Rc6 caches; no package or release replay')
(E/'FGl_attempts.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in rows))
for name,obj in [('FGl_validation.json',result),('FGl_sources.json',covered),('FGl_theorems.json',theorems),('FGl_axioms.json',audits)]:
    (E/name).write_text(json.dumps(obj,indent=2)+'\n')
print(json.dumps(result,indent=2))
