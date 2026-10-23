#!/usr/bin/env python3
"""Verbatim client/retry control vs owned recursion, verified callee boundaries."""
import hashlib,json,subprocess,sys
from pathlib import Path
R=Path(__file__).resolve().parent.parent
name=sys.argv[1];assert name.startswith('client-owned-v')
out=R/'native'/name;out.mkdir(parents=True,exist_ok=False)
def extract(path,name):
    text=Path(path).read_text();start=text.index('pub fn '+name+'(');b=text.index('{',start);depth=1;i=b+1
    while depth:
        depth+=(text[i]=='{')-(text[i]=='}');i+=1
    return text[start:i]+'\n'
funcs={'RealR1_native_retry.rs':extract('crates/aspis-r1-cost-probe/src/prover.rs','prove_masked_retrying_with'),
       'RealR1_native_client.rs':extract('crates/aspis-r1-cost-probe/src/RealR1_client.rs','prove_for_proof_accounts')}
for n,s in funcs.items():(out/n).write_text(s)
files={p.name:p.read_bytes() for p in (R/'harness/RealR1_retry').iterdir() if p.is_file()}
files.update({n:s.encode() for n,s in funcs.items()})
pins=dict(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
          files={n:hashlib.sha256(s).hexdigest() for n,s in files.items()},
          contracts=['E1 selected 64-byte API: source identity with parts 41-43','complete attempt body result and mutable store effects: R2/R3',
                     'reservation primitive: faithful-reservation-v4 and E2'],
          scope='Control and ordered callback/entropy/body call effects only. No native leakage or probability claim.')
(out/'inputs.json').write_text(json.dumps(pins,indent=2)+'\n')
H='dombarker@100.108.41.90';W='/home/dombarker/project-offloads/codex-cx-real-r1-20261023'
subprocess.run(['ssh',H,'mkdir -p '+W+'/retry-gate'],check=True)
for n,s in files.items():
    subprocess.run(['ssh',H,'cat > '+W+'/retry-gate/'+n],input=s,check=True)
remote=f'''
import os,subprocess,time
from pathlib import Path
W=Path({W!r})
def reserved():
    caps=[]
    for p in Path('/sys/fs/cgroup').rglob('memory.max'):
        try:
            v=p.read_text().strip()
            if v!='max' and (p.parent/'cgroup.procs').read_text().strip():caps.append(int(v))
        except OSError:pass
    return sum(caps)
start=time.monotonic()
while reserved()+8*2**30>55*2**30:
    assert time.monotonic()-start<1800
    print('Waiting for retry gate reservation',flush=True);time.sleep(15)
os.chdir(W/'retry-gate')
os.environ.update(PATH='/home/dombarker/.cargo/bin:'+os.environ['PATH'],CARGO_TARGET_DIR=str(W/'retry-target'),CARGO_BUILD_JOBS='4',CARGO_PROFILE_DEV_OPT_LEVEL='3',CARGO_NET_OFFLINE='true',RUSTFLAGS='-C opt-level=3 -C link-arg=-Wl,--threads=4')
cmd=['cargo','kani','-j','4','--lib','--exact','--harness','proofs::selected_client_owned','-Z','unstable-options','--output-format','terse','--cbmc-args','--unwinding-assertions','--object-bits','12']
raise SystemExit(subprocess.run(['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(W/'harness/RealR1_capped.py'),str(W/'native'/{name!r}),'Optimized Kani compile and eight-step control equivalence; crypto and IO are stated contracts','--','timeout','600',*cmd]).returncode)
'''
status=subprocess.run(['ssh',H,'python3 -'],input=remote,text=True).returncode
for n in ['receipt.json','time.log','stdout.log','stderr.log']:
    subprocess.run(['scp',H+':'+W+'/native/'+name+'/'+n,str(out/n)],check=True)
sys.exit(status)
