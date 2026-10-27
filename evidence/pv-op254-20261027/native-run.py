from pathlib import Path
import subprocess,json,hashlib,re,time,sys
H=Path('/home/dombarker/project-offloads/codex-pv-op254-20261027')
C=Path('/home/dombarker/project-offloads/codex-pv-batch1-20261027/candidate/src')
label=sys.argv[1];R=H/label;R.mkdir(exist_ok=False)
checks=[]
for x in json.loads((H/'native-core-pins.json').read_text()):
 p=C/x['path'];actual=hashlib.file_digest(p.open('rb'),'sha256').hexdigest() if p.exists() else None
 checks.append(dict(**x,actual=actual,match=actual==x['sha256']))
(R/'source-verification.json').write_text(json.dumps(checks,indent=2)+'\n')
assert all(x['match'] for x in checks),'candidate dependency bytes differ'
with (R/'reservation.json').open('w') as log:
 a=subprocess.run(['python3',str(H/'Port13GATE_admission.py')],stdout=log,stderr=subprocess.STDOUT)
assert a.returncode==0 and json.loads((R/'reservation.json').read_text()).get('allowed') is True,'refused before scope'
cmd=['systemd-run','--user','--scope','--quiet','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','/usr/bin/time','-v','-o',str(R/'time.log'),'taskset','--cpu-list','0-3','/home/dombarker/.cargo/bin/cargo','run','--release','--offline','--manifest-path',str(H/'native/Cargo.toml'),'--target-dir',str(H/'native-target'),'-j','4']
start=time.monotonic()
with (R/'out.log').open('w') as log:r=subprocess.run(cmd,stdout=log,stderr=subprocess.STDOUT)
tm=(R/'time.log').read_text();out=(R/'out.log').read_text()
def metric(p):
 m=re.search(p,tm);return m.group(1) if m else None
receipt=dict(target='native finite differential gate: powers/sum/pole',command=cmd,exit=r.returncode,wall_seconds=time.monotonic()-start,peak_rss_kib=metric(r'Maximum resident set size \(kbytes\): (\d+)'),swap=metric(r'Swaps: (\d+)'),source_revision=(H/'proof-revision.txt').read_text().strip(),print_axioms='N/A native execution',phase='optimized compilation then named finite differential execution',source_checks=len(checks),results=out.splitlines()[-1] if out else '')
(R/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt));sys.exit(r.returncode)
