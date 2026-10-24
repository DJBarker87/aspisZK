#!/usr/bin/env python3
import pathlib,json,subprocess,sys,hashlib,shlex
R=pathlib.Path(__file__).resolve().parents[2];T=R/'tools/port18coherence-20261024';E=R/'evidence/port18coherence-20261024';L=R/'docs/research/100bit-spend-path-20261013/lean'
H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-port18coherence-20261024'
n=1+len(list(T.glob('lean-*.json')));assert n<=81;a=f'lean-{n:03d}';m=sys.argv[1];assert m.startswith('Port18COHERENCE_')
x=json.loads((R/'tools/port17release-20261024/lean-024.json').read_text());x.update(attempt=a,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),sources=[m+'.lean'],timeout=180)
x['command'][-3:]=['-o',m+'.olean',m+'.lean'];x['env']['LEAN_PATH']=B+':'+x['env']['LEAN_PATH'];x['deps_fingerprint']={'basis':'pinned Port17 root path; diagnostic object paths are in hashed input.tsv','input_sha256':hashlib.sha256((T/'input.tsv').read_bytes()).hexdigest(),'lean_binary':'recorded in host receipt'}
x['env']['PORT18_SNAPSHOT']=B+'/snapshots/root'
c=T/(a+'.json');c.write_text(json.dumps(x,indent=2)+'\n')
def run(args,**kw):return subprocess.run(args,check=True,**kw)
run(['ssh',H,'mkdir','-p',B]);run(['scp','-q',str(c),str(L/(m+'.lean')),str(T/'input.tsv'),str(T/'Port18COHERENCE_run_host.py'),str(T/'Port18COHERENCE_admission.py'),H+':'+B+'/'])
# Both snapshots taken while holding shared lock; go snapshot immediately precedes launch.
inner=f'python3 Port18COHERENCE_admission.py > {a}-before.json && python3 Port18COHERENCE_admission.py > {a}-go.json && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 Port18COHERENCE_run_host.py {a}.json'
r=subprocess.run(['ssh',H,'cd '+B+' && flock /tmp/aspis-r0-lean.lock sh -c '+shlex.quote(inner)],capture_output=True,text=True)
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
for f in [a+'-before.json',a+'-go.json',a]:subprocess.run(['scp','-qr',H+':'+B+'/'+f,str(E)])
print(r.stdout,r.stderr);sys.exit(r.returncode)
