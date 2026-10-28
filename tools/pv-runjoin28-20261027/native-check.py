"""Read deterministic source fixture words with a capped optimized native probe."""
import pathlib,subprocess,sys,json,shlex,hashlib,datetime
R=pathlib.Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin28-20261027';host='dombarker@100.108.41.90';H='/home/dombarker/project-offloads/codex-pv-runjoin-20261026'
name=sys.argv[1];assert not (E/(name+'.json')).exists()
prior_refusals=[json.loads(p.read_text()) for p in E.glob('*refusal*.json')]
if prior_refusals:
 last=max(datetime.datetime.fromisoformat(r['utc']) for r in prior_refusals)
 remaining=180-(datetime.datetime.now(datetime.timezone.utc)-last).total_seconds()
 if remaining>0:
  print(f'WAIT: {remaining:.1f}s remain before another admission check; no launch',flush=True)
  sys.exit(77)
def ssh(s):return subprocess.run(['ssh',host,s],capture_output=True,text=True)
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
subprocess.run(['scp','-q',f'{host}:{H}/evidence/{name}-reservation.json',str(E)],check=True)
prefix='tools/pv-runjoin28-20261027/frontier-probe'
r=ssh('mkdir -p '+H+'/runjoin27-native-source/'+prefix);assert r.returncode==0
paths=[prefix+'/'+n for n in ['Cargo.toml','main.rs']]
for p in paths:subprocess.run(['scp','-q',str(R/p),f'{host}:{H}/runjoin27-native-source/{p}'],check=True)
subprocess.run(['scp','-q',str(R/'tools/pv-runjoin12-20261027/kani-receipt.py'),f'{host}:{H}/evidence/pv28-native-receipt.py'],check=True)
cmd=['cargo','run','--release','--offline','--manifest-path',H+'/runjoin27-native-source/'+prefix+'/Cargo.toml','-j','4']
record=dict(target=cmd,worker_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),expected_time='optimized library compilation then the fixed input commitment and path parents; native canonical control, active frontier representation and compiler/codec guard probe; no dense arithmetic gate',source_sha256={p:hashlib.sha256((R/p).read_bytes()).hexdigest() for p in paths})
(E/(name+'.json')).write_text(json.dumps(record,indent=2)+'\n')
scope=['systemd-run','--user','--scope','--quiet','--unit='+name,'-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','env','PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin','CARGO_TARGET_DIR='+H+'/target-charon','CARGO_BUILD_JOBS=4','RUSTFLAGS=-C opt-level=3 -C link-arg=-Wl,--threads=4','PV8_SOURCE_DIR='+H+'/runjoin27-native-source','python3',H+'/evidence/pv28-native-receipt.py',H+'/evidence/'+name,'timeout','240',*cmd]
r=ssh(shlex.join(scope));(E/(name+'-scope.log')).write_text(r.stdout+r.stderr)
subprocess.run(['scp','-qr',f'{host}:{H}/evidence/{name}',str(E)],check=True)
p=E/name/'receipt.json';d=json.loads(p.read_text());native_pins=d['source_sha256'];d.update(record);d['axioms']='N/A: deterministic native data extraction, not a Lean theorem';d['executed_source_sha256']=native_pins;d['full_native_source_check']='native-source-check.json';d['native_finding']='active noncanonical frontier preparation guard candidate';p.write_text(json.dumps(d,indent=2)+'\n')
print((E/name/'out.log').read_text()[-3500:]);sys.exit(r.returncode)
