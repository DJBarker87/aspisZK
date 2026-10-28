"""Read deterministic source fixture words with a capped optimized native probe."""
import pathlib,subprocess,sys,json,shlex,hashlib,datetime,time
R=pathlib.Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin31-20261028';host='dombarker@100.108.41.90';H='/home/dombarker/project-offloads/codex-pv-runjoin-20261026'
assert json.loads((E/'pv31-lane-reference-charon-03.llbc').read_text())['has_errors'] is False
name=sys.argv[1];assert not (E/(name+'.json')).exists()
prior_refusals=[json.loads(p.read_text()) for p in E.glob('*refusal*.json')]
if prior_refusals:
 last=max(datetime.datetime.fromisoformat(r['utc']) for r in prior_refusals)
 remaining=180-(datetime.datetime.now(datetime.timezone.utc)-last).total_seconds()
 if remaining>0:
  print(f'WAIT: {remaining:.1f}s remain before another admission check; no launch',flush=True)
  sys.exit(77)
def transport(cmd, **kw):
 for retry in range(11):
  r=subprocess.run(cmd, **kw)
  if r.returncode!=255:return r
  with (E/'native-transport-retries.jsonl').open('a') as f:f.write(json.dumps(dict(name=name,retry=retry,command=cmd))+'\n')
  if retry==10:raise RuntimeError('ten transient transport retries exhausted')
  print('transient transport; waiting 60 seconds before read-only/prelaunch retry',flush=True);time.sleep(60)
 return r
def ssh(s):return transport(['ssh',host,s],capture_output=True,text=True)
# Read-only check of the exact native dependency source tree before execution.
files=sorted(str(p.relative_to(R)) for crate in ['aspis-core','aspis-statement'] for p in (R/'crates'/crate/'src').rglob('*.rs'))
files+=sorted(str(p.relative_to(R)) for name in ['writers','blockwriters','poseidon'] for p in (R/'docs/research/v8-r0-zk-20261009/refine'/name).rglob('*.rs'))
files+=['Cargo.toml','Cargo.lock','crates/aspis-core/Cargo.toml','crates/aspis-statement/Cargo.toml']
expected={p:hashlib.sha256((R/p).read_bytes()).hexdigest() for p in files}
code="import pathlib,json,hashlib;root=pathlib.Path("+repr(H+'/runjoin27-native-source')+");print(json.dumps({p:hashlib.sha256((root/p).read_bytes()).hexdigest() for p in "+repr(files)+"}))"
r=ssh('python3 -c '+shlex.quote(code));assert r.returncode==0,r.stderr
actual=json.loads(r.stdout);mismatches=[p for p,h in expected.items() if actual.get(p)!=h]
(E/'native-source-check.json').write_text(json.dumps(dict(expected=expected,actual=actual,mismatches=mismatches),indent=2)+'\n')
assert not mismatches,mismatches
r=ssh(f'python3 {H}/reservation-existing.py {H}/evidence/{name}-reservation.json > {H}/evidence/{name}-reservation.log 2>&1\nreservation_status=$?\ncat {H}/evidence/{name}-reservation.log\nexit $reservation_status');(E/(name+'-reservation.log')).write_text(r.stdout+r.stderr);a=json.loads(r.stdout.strip().splitlines()[-1])
if r.returncode != 0 or not a['allowed']:
 (E/(name+'-refusal.json')).write_text(json.dumps(a,indent=2)+'\n');print(a);sys.exit(78)
transport(['scp','-q',f'{host}:{H}/evidence/{name}-reservation.json',str(E)],check=True)
probe='outer-aeneas'
cmd=['/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/rng-extractor/candidate-007/main.exe','-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','PV_RunJoin_Lane31','-dest',H+'/evidence/'+name+'-generated','-split-files','-emit-json',H+'/evidence/pv31-lane-reference-charon-03.llbc']
paths=[]
transport(['scp','-q',str(R/'tools/pv-runjoin12-20261027/kani-receipt.py'),f'{host}:{H}/evidence/pv31-native-receipt.py'],check=True)
record=dict(target=cmd,worker_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),expected_time='Aeneas translation of the error-free pinned optimized LLBC; no Rust compilation or arithmetic gate',source_sha256={p:hashlib.sha256((R/p).read_bytes()).hexdigest() for p in paths})
(E/(name+'.json')).write_text(json.dumps(record,indent=2)+'\n')
scope=['systemd-run','--user','--scope','--quiet','--unit='+name,'-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','env','PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin','CARGO_TARGET_DIR='+H+'/target-charon','CARGO_BUILD_JOBS=4','RUSTFLAGS=-C opt-level=3 -C link-arg=-Wl,--threads=4','PV8_SOURCE_DIR='+H+'/runjoin27-native-source','python3',H+'/evidence/pv31-native-receipt.py',H+'/evidence/'+name,'timeout','240',*cmd]
r=subprocess.run(['ssh',host,shlex.join(scope)],capture_output=True,text=True);(E/(name+'-scope.log')).write_text(r.stdout+r.stderr)
transport(['scp','-qr',f'{host}:{H}/evidence/{name}',str(E)],check=True)
p=E/name/'receipt.json';d=json.loads(p.read_text());native_pins=d['source_sha256'];d.update(record);d['axioms']='N/A: deterministic native data extraction, not a Lean theorem';d['executed_source_sha256']=native_pins;d['full_native_source_check']='native-source-check.json';d['native_finding']=probe;p.write_text(json.dumps(d,indent=2)+'\n')
transport(['scp','-qr',f'{host}:{H}/evidence/{name}-generated',str(E)],check=True) if d['exit']==0 else None
print((E/name/'out.log').read_text()[-5000:]);sys.exit(0 if d['exit']==0 else 1)
