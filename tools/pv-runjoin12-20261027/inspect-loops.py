"""Read deterministic source fixture words with a capped optimized native probe."""
import pathlib,subprocess,sys,json,shlex,hashlib
R=pathlib.Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin12-20261027';host='dombarker@100.108.41.90';H='/home/dombarker/project-offloads/codex-pv-runjoin-20261026'
name=sys.argv[1];assert not (E/(name+'.json')).exists()
def ssh(s):return subprocess.run(['ssh',host,s],capture_output=True,text=True)
r=ssh(f'python3 {H}/reservation-existing.py {H}/evidence/{name}-reservation.json > {H}/evidence/{name}-reservation.log 2>&1\ncat {H}/evidence/{name}-reservation.log');(E/(name+'-reservation.log')).write_text(r.stdout+r.stderr);a=json.loads(r.stdout.strip().splitlines()[-1])
if not a['allowed']:
 (E/(name+'-refusal.json')).write_text(json.dumps(a,indent=2)+'\n');print(a);sys.exit(78)
subprocess.run(['scp','-q',f'{host}:{H}/evidence/{name}-reservation.json',str(E)],check=True)
prefix='tools/pv-runjoin12-20261027'
r=ssh('mkdir -p '+H+'/frozen/'+prefix);assert r.returncode==0
paths=[]
for p in paths:subprocess.run(['scp','-q',str(R/p),f'{host}:{H}/frozen/{p}'],check=True)
subprocess.run(['scp','-q',str(R/'tools/pv-runjoin12-20261027/kani-receipt.py'),f'{host}:{H}/evidence/pv12-native-receipt.py'],check=True)
cmd=['/home/dombarker/.kani/kani-0.67.0/bin/cbmc',H+'/target/kani/x86_64-unknown-linux-gnu/debug/deps/aspis_statement-d7af723322e01b64__RNvNtNtNtNtCscTz6BOl5pFg_15aspis_statement7pool_v124pair_forest_copy_builder14records_proofs18pv_runjoin12_exact14transfer_tight.out','--show-loops']
record=dict(target=cmd,worker_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_revision='retained Run04 goto model; originating Rust source pins in invocation04',expected_time='read retained2.6MB goto loop metadata only; no verification or compilation',source_sha256={p:hashlib.sha256((R/p).read_bytes()).hexdigest() for p in paths})
(E/(name+'.json')).write_text(json.dumps(record,indent=2)+'\n')
scope=['systemd-run','--user','--scope','--quiet','--unit='+name,'-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','env','PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin','CARGO_TARGET_DIR='+H+'/target-charon','CARGO_BUILD_JOBS=4','RUSTFLAGS=-C opt-level=3 -C link-arg=-Wl,--threads=4','PV8_SOURCE_DIR='+H+'/frozen','python3',H+'/evidence/pv12-native-receipt.py',H+'/evidence/'+name,'timeout','240',*cmd]
r=ssh(shlex.join(scope));(E/(name+'-scope.log')).write_text(r.stdout+r.stderr)
subprocess.run(['scp','-qr',f'{host}:{H}/evidence/{name}',str(E)],check=True)
p=E/name/'receipt.json';d=json.loads(p.read_text());d['executed_target']=d['target'];d.update(record);d['axioms']='N/A: metadata inspection, no verification';d['classification']='CBMC --show-loops inspection only; zero Kani verification runs';p.write_text(json.dumps(d,indent=2)+'\n')
print('loop metadata collected: '+str(E/name/'out.log'));sys.exit(r.returncode)
