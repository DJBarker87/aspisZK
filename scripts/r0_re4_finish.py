#!/usr/bin/env python3
"""Final preservation and count evidence. Never repeats a CU measurement."""
import hashlib,json,os,subprocess,sys
from pathlib import Path
out=Path('results/r0-e2e-20261009/re4')
stage=sys.argv[1]
assert json.loads((out/f'{stage}-stack.json').read_text())['exit_status']==0
for fixture in ['transfer','withdrawal']:
    r=json.loads((out/f'{stage}-diagnostic/{fixture}-diagnostic-1.json').read_text())
    assert r['verifier_completed'] and r['sbf_heap_high_water_bytes']<=262144
plan={'driver_build':'optimized compilation','regeneration':'optimized proof generation, once for each fixture, then exact byte comparison','counts':'native operation accounting, once per fixture; no SBF measurement','caps':{'MemoryHigh':'4G','MemoryMax':'6G','MemorySwapMax':0}}
assert not (out/'finish-plan.json').exists()
(out/'finish-plan.json').write_text(json.dumps(plan,indent=2)+'\n')
def run(label,*cmd): subprocess.run(['python3','scripts/r0_re4_run.py',label,*cmd],check=True)
run('final-driver','cargo','build','--release','--locked','--manifest-path','tools/v8-state-only-cu-probe/Cargo.toml','--bin','r0-e2e-cu-probe')
target=Path('/home/dombarker/project-offloads/aspis-r0-semantics-20261009/target/release')
for fixture in ['transfer','withdrawal']:
    run('regenerate-'+fixture,str(target/'r0-e2e-cu-probe'),'fixture',str(out/'regenerated'),fixture)
    for suffix in ['proof.bin','public.bin']:
        name=fixture+'.'+suffix
        assert (out/'regenerated'/name).read_bytes()==(out/'fixtures'/name).read_bytes(), 'STOP: prover bytes changed: '+name
run('final-counts-build','cargo','build','--release','--locked','--manifest-path','tools/v8-state-only-cu-probe/Cargo.toml','--features','r0-op-count','--bin','r0-counts')
for fixture in ['transfer','withdrawal']:
    run('counts-'+fixture,str(target/'r0-counts'),str(out/'fixtures'),fixture,str(out/f'counts-{fixture}-ops.json'))
keys=[]
for p in out.rglob('*.json'):
    if 'keypair' in p.name or 'payer' in p.name:
        p.chmod(0o600)
        keys.append({'path':str(p.resolve()),'mode':oct(p.stat().st_mode&0o777),'retained':True,'cleanup':False})
env={'host':os.uname().nodename,'kernel':os.uname().release,'keys':keys,'chain_transactions':0,'safe_host_reservation_bytes':50*2**30}
for cmd in [['/home/dombarker/.cargo/bin/rustc','-Vv'],['/home/dombarker/.local/share/solana/install/releases/3.1.13/solana-release/bin/cargo-build-sbf','--version']]:
    env[' '.join(cmd)]=subprocess.check_output(cmd,text=True)
(out/'environment-re4.json').write_text(json.dumps(env,indent=2)+'\n')
