import json, hashlib, sys, subprocess, resource, signal, time
from pathlib import Path
from datetime import datetime, timezone
signal.alarm(20)
start=time.monotonic(); utc=datetime.now(timezone.utc).isoformat()
p=Path(__file__).resolve().parent
sha=lambda f:hashlib.sha256(Path(f).read_bytes()).hexdigest()
r=json.loads((p/'FinalNativeGateAncestry-receipt.json').read_text())
a=json.loads((p/'FinalNativeGateAncestry-analysis.json').read_text())
plans=[json.loads((p/n).read_text()) for n in ['FinalNativeGateAncestry-plan.json','FinalNativeGateAncestry-plan-v2.json','FinalNativeGateAncestry-plan-v3.json']]
assert all(x['argv']==r['argv'] for x in plans)
assert r['spawn_attempts']==1 and r['ssh_exit']==1 and r['termination_reason'] is None
assert sum(v['size'] for v in r['output'].values())==536
for stream,v in r['output'].items():
    f=p/('FinalNativeGateAncestry-'+stream+'.txt')
    assert f.stat().st_size==v['size'] and sha(f)==v['sha256']
    assert f.read_bytes()==(Path(r['capture'])/(stream+'.bin')).read_bytes()
assert sha(p/'FinalNativeGateAncestry-capture-v3.py')==r['script_sha256']==plans[-1]['capture_script_sha256']
assert sha(plans[-1]['receiver']['path'])==plans[-1]['receiver']['sha256']
assert [x['check_directory_pass'] for x in a['rows']]==[True,True,True,False,False,None]
assert [x['permissions_octal'] for x in a['rows'][:5]]==['0755','0755','0750','0775','0775']
changed=subprocess.check_output(['git','diff','--name-only','a29e6496d8','HEAD'],text=True).splitlines()
allowed='docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/final-native-gate/FinalNativeGateAncestry-'
assert all(x.startswith(allowed) for x in changed)
u=resource.getrusage(resource.RUSAGE_SELF);c=resource.getrusage(resource.RUSAGE_CHILDREN)
assert u.ru_maxrss+c.ru_maxrss<512*2**20
record=dict(command=[sys.executable,str(Path(__file__).resolve())],utc=utc,end_utc=datetime.now(timezone.utc).isoformat(),revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),exit=0,wall_seconds=time.monotonic()-start,interpreter_sha256=sha(sys.executable),source_sha256=sha(__file__),self_peak_RSS_bytes_macos=u.ru_maxrss,children_peak_RSS_bytes_macos=c.ru_maxrss,conservative_sum_of_peaks_bytes=u.ru_maxrss+c.ru_maxrss,self_swap=u.ru_nswap,children_swap=c.ru_nswap,axioms='N/A',checks='capture complete and identical to private bytes; same exact SSH argv across all preregistrations; one SSH spawn; retained pre-SSH failures; receiver unchanged; per-path predicates; committed path boundary',dependencies={str(f):dict(size=f.stat().st_size,sha256=sha(f)) for f in sorted(p.glob('FinalNativeGateAncestry-*')) if f.name!='FinalNativeGateAncestry-verification.json'})
(p/'FinalNativeGateAncestry-verification.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:record[k] for k in ['exit','wall_seconds','conservative_sum_of_peaks_bytes','self_swap','children_swap','axioms']}))
