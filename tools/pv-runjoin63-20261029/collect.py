"""Collect original module logs and summarize focused receipts read-only."""
from pathlib import Path
import subprocess,json,hashlib,lzma,shlex
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin63-20261029'
records=[v for p in sorted(E.glob('modules-*.json')) for v in json.loads(p.read_text())]
code='''import sys,json,pathlib,hashlib
out=[]
for v in json.load(sys.stdin):
 p=pathlib.Path(v['output_path']);b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==v['output_sha256'];out.append(dict(module=v['module'],path=str(p),sha256=v['output_sha256'],text=b.decode()))
print(json.dumps(out))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(records),text=True,capture_output=True,check=True)
b=r.stdout.encode();(E/'original-module-logs.json.xz').write_bytes(lzma.compress(b));(E/'original-module-logs.json.sha256').write_text(hashlib.sha256(b).hexdigest()+'\n')
receipts=[json.loads(p.read_text()) for p in sorted(E.glob('receipt-*.json'))]
summary=dict(attempts=len(receipts),accepted=sum(v['accepted'] for v in receipts),rejected=sum(not v['accepted'] for v in receipts),kani=0,ids=[v['attempt'] for v in receipts],host_wall_seconds=sum(v['host_wall_seconds'] for v in receipts),peak_rss_bytes=max(v['peak_rss_bytes'] for v in receipts),swaps=sum(v['swaps'] for v in receipts),refusals=len(list(E.glob('refusal-*.json'))),guard_sha256=hashlib.sha256((R/'tools/pv-runjoin63-20261029/compile.py').read_bytes()).hexdigest(),rows_removed=[],endpoint_changed=0,native_nonemptiness_proved=False,nondegenerate_model_witness_proved=False)
(E/'SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
failed=[dict(module=v['module'],revision=v['source_revision'],sha256=v['source_sha256'],exit=v['exit']) for v in records if not v['accepted']]
(E/'retained-failed-sources.json').write_text(json.dumps(failed,indent=2)+'\n')
