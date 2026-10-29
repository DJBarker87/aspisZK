"""Fail closed: two declarations, byte-identical headers, exactly one proof edit."""
from pathlib import Path
import subprocess,re,json,hashlib
D=Path(__file__).parent
path='docs/research/v8-r0-zk-20261009/lean/R1Z/PrivacyR1HeadlineV2.lean'
git=lambda *a:subprocess.check_output(['git',*a]);sha=lambda b:hashlib.sha256(b).hexdigest()
a=git('cat-file','blob','431494fb8678733178af8c5c58cb18fbcb49f3b9');b=git('show','HEAD:'+path)
headers=lambda raw:[raw[m.start():raw.index(b':= by',m.start())+2] for m in re.finditer(rb'(?m)^theorem\s+',raw)]
assert len(headers(a))==len(headers(b))==2 and headers(a)==headers(b)
assert a.replace(b'      rfl)\n',b'      )\n',1)==b
assert not re.search(rb'(?m)^(def|abbrev|instance|structure|inductive|opaque|axiom|lemma)\s',a)
assert git('show','e030a78a73^:'+path)==a
for r in ['research','b02602fa23','e030a78a73']:assert git('show',r+':'+path)==b
record=json.loads((D/'statement-identity.json').read_text());assert record['ejr_sha256']==sha(a) and record['tracked_sha256']==sha(b)
for s,r in zip(headers(b),record['declarations']):assert sha(s)==r['signature_sha256']
print('Both complete declaration signatures byte-identical; only proof text differs; history/research/candidate verified')
