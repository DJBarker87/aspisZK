"""One capped native probe on source-hash-checked frozen dependencies."""
from pathlib import Path
import json,subprocess,shlex,hashlib,datetime,sys,time
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-l2c-20261028/resume-d371';H='/home/dombarker/project-offloads/codex-pv-l2c-20261028';host='dombarker@100.108.41.90';B=H+'/native-source'
name=sys.argv[1]
refusal=E/(name+'-refusal.json')
if refusal.exists():
 remaining=180-(datetime.datetime.now(datetime.timezone.utc)-datetime.datetime.fromisoformat(json.loads(refusal.read_text())['utc'])).total_seconds()
 if remaining>0:print('Cooldown remaining',remaining);sys.exit(77)
assert not (E/(name+'-invocation.json')).exists()
def ssh(s,payload=None):
 for retry in range(10):
  p=subprocess.run(['ssh',host,s],input=payload,text=True,capture_output=True)
  with (E/(name+'-transport.jsonl')).open('a') as f:
   f.write(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),command=s,exit=p.returncode,stdout=p.stdout,stderr=p.stderr))+'\n')
  if p.returncode!=255:return p
  if (E/(name+'-invocation.json')).exists():return p
  if retry==9:return p
  print('Prelaunch SSH255; waiting 60 seconds before retry of the same transport step',flush=True)
  time.sleep(60)
 return p

files=sorted(str(p.relative_to(R)) for crate in ['aspis-core','aspis-statement','aspis-prover','aspis-r1-cost-probe'] for p in (R/'crates'/crate/'src').rglob('*.rs'))
files+=sorted(str(p.relative_to(R)) for n in ['writers','blockwriters','poseidon'] for p in (R/'docs/research/v8-r0-zk-20261009/refine'/n).rglob('*.rs'))
files+=sorted(str(p.relative_to(R)) for p in (R/'docs/research/v8-r0-zk-20261009/z4').rglob('*.rs'))
files+=['Cargo.toml','Cargo.lock','crates/aspis-core/Cargo.toml','crates/aspis-statement/Cargo.toml','crates/aspis-prover/Cargo.toml','crates/aspis-r1-cost-probe/Cargo.toml','docs/research/v8-r0-zk-20261009/z4/Cargo.toml']
expected={p:hashlib.sha256((R/p).read_bytes()).hexdigest() for p in files}
code='import pathlib,json,hashlib,sys;r=pathlib.Path('+repr(B)+');print(json.dumps({p:hashlib.sha256((r/p).read_bytes()).hexdigest() for p in json.load(sys.stdin)}))'
p=ssh('python3 -c '+shlex.quote(code),json.dumps(files));assert p.returncode==0,p.stderr
actual=json.loads(p.stdout);assert actual==expected
(E/(name+'-source-check.json')).write_text(json.dumps(dict(expected=expected,actual=actual),indent=2)+'\n')
p=ssh(f'python3 /home/dombarker/project-offloads/codex-pv-runjoin-20261026/reservation-existing.py {H}/evidence/{name}-reservation.json > {H}/evidence/{name}-reservation.log 2>&1\ns=$?\ncat {H}/evidence/{name}-reservation.log\nexit $s')
(E/(name+'-reservation.log')).write_text(p.stdout+p.stderr)
assert p.returncode!=255, 'ten prelaunch transport attempts exhausted; no native scope submitted'
assert p.stdout.strip(), 'reservation produced no JSON; inspect retained transport log'
gate=json.loads(p.stdout.strip().splitlines()[-1])
if p.returncode or not gate['allowed']:
 gate['utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();(E/(name+'-refusal.json')).write_text(json.dumps(gate));sys.exit(78)
assert ssh(f'mkdir -p {H}/decoder-probe').returncode==0
for f in ['main.rs','Cargo.toml','hash_reference.rs','domain_constants.rs','frozen_empty_roots.rs']:
 subprocess.run(['scp','-q',str(R/'tools/pv-l2c-20261028/decoder-probe'/f),f'{host}:{H}/decoder-probe/{f}'],check=True)
subprocess.run(['scp','-q',str(R/'tools/pv-l2c-20261028/native-receipt.py'),f'{host}:{H}/native-receipt.py'],check=True)
assert ssh(f'cp {B}/Cargo.lock {H}/decoder-probe/Cargo.lock').returncode==0
cmd=['systemd-run','--user','--scope','--quiet','--unit=l2c-'+name,'-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','env','PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin','CARGO_TARGET_DIR='+H+'/decoder-probe-target','CARGO_BUILD_JOBS=4','RUSTFLAGS=-C opt-level=3 -C link-arg=-Wl,--threads=4','PV8_SOURCE_DIR='+H+'/decoder-probe','PV_L2C_PIN_FILES=main.rs:Cargo.toml:Cargo.lock:hash_reference.rs:domain_constants.rs:frozen_empty_roots.rs','PV_L2C_EXPECTED_TIME='+('Optimized compilation then four lane field differentials and four checkpoint roundtrips with 704 noncanonical account rejections; no proof generation or elimination' if name.startswith('account-') else 'Optimized compilation then scalar and digest decoder boundary cases and 128 generated-key range samples and 512 same-input native/owned-external hash comparisons; no proof generation or elimination'),'PV_L2C_EVIDENCE_CLASS=Native finite decoder/generator validation; no universal theorem, no Kani','python3',H+'/native-receipt.py',H+'/evidence/'+name,'timeout','240','cargo','run','--release','--offline','-j','4']+(['--','account-only'] if name.startswith('account-') else [])
(E/(name+'-invocation.json')).write_text(json.dumps(dict(command=cmd,runner_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),receipt_helper_sha256=hashlib.sha256((R/'tools/pv-l2c-20261028/native-receipt.py').read_bytes()).hexdigest(),revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),reservation=gate),indent=2)+'\n')
p=ssh(shlex.join(cmd));(E/(name+'-scope.log')).write_text(p.stdout+p.stderr)
assert p.returncode!=255,'Submitted: recover read-only, do not resubmit'
subprocess.run(['scp','-qr',f'{host}:{H}/evidence/{name}',str(E)],check=True)
print((E/name/'out.log').read_text()[-10000:]);sys.exit(p.returncode)
