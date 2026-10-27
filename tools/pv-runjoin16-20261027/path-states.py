"""Read deterministic source fixture words with a capped optimized native probe."""
import pathlib,subprocess,sys,json,shlex,hashlib
R=pathlib.Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin16-20261027';host='dombarker@100.108.41.90';H='/home/dombarker/project-offloads/codex-pv-runjoin-20261026'
name=sys.argv[1];assert not (E/(name+'.json')).exists()
def ssh(s):return subprocess.run(['ssh',host,s],capture_output=True,text=True)
r=ssh(f'python3 {H}/reservation-existing.py {H}/evidence/{name}-reservation.json > {H}/evidence/{name}-reservation.log 2>&1\nreservation_status=$?\ncat {H}/evidence/{name}-reservation.log\nexit $reservation_status');(E/(name+'-reservation.log')).write_text(r.stdout+r.stderr);a=json.loads(r.stdout.strip().splitlines()[-1])
if r.returncode != 0 or not a['allowed']:
 (E/(name+'-refusal.json')).write_text(json.dumps(a,indent=2)+'\n');print(a);sys.exit(78)
subprocess.run(['scp','-q',f'{host}:{H}/evidence/{name}-reservation.json',str(E)],check=True)
prefix='tools/pv-runjoin16-20261027'
r=ssh('mkdir -p '+H+'/frozen/'+prefix);assert r.returncode==0
paths=[prefix+'/'+n for n in ['path-states.rs','root-states-host.py']]
for p in paths:subprocess.run(['scp','-q',str(R/p),f'{host}:{H}/frozen/{p}'],check=True)
subprocess.run(['scp','-q',str(R/'tools/pv-runjoin16-20261027/kani-receipt.py'),f'{host}:{H}/evidence/pv16-path-receipt.py'],check=True)
cmd=['python3',H+'/frozen/'+prefix+'/root-states-host.py',H+'/frozen/'+prefix+'/path-states.rs',H+'/evidence/'+name+'-generator']
record=dict(target=cmd,worker_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_revision='bounded mathematical generator transcription; normative table pinned ed1c1cef71',expected_time='rustc opt-level3 then24 bounded mathematical membership-node permutation cells; numeric data only, no source gate',source_sha256={p:hashlib.sha256((R/p).read_bytes()).hexdigest() for p in paths})
(E/(name+'.json')).write_text(json.dumps(record,indent=2)+'\n')
scope=['systemd-run','--user','--scope','--quiet','--unit='+name,'-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','env','PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin','CARGO_TARGET_DIR='+H+'/target-charon','CARGO_BUILD_JOBS=4','RUSTFLAGS=-C opt-level=3 -C link-arg=-Wl,--threads=4','PV8_SOURCE_DIR='+H+'/frozen','python3',H+'/evidence/pv16-path-receipt.py',H+'/evidence/'+name,'timeout','240',*cmd]
r=ssh(shlex.join(scope));(E/(name+'-scope.log')).write_text(r.stdout+r.stderr)
subprocess.run(['scp','-qr',f'{host}:{H}/evidence/{name}',str(E)],check=True)
p=E/name/'receipt.json';d=json.loads(p.read_text());d['executed_target']=d['target'];d.update(record);d['axioms']='N/A: mathematical certificate generation, to be checked by Lean';d['classification']='numeric model data only; not source execution/equivalence';p.write_text(json.dumps(d,indent=2)+'\n')
print('fixture states collected: '+str(E/name/'out.log'));sys.exit(r.returncode)
