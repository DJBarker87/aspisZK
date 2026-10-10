#!/usr/bin/env python3
"""Build-host launcher: source audit, aggregate reservation, capped recorder."""
import hashlib, json, os, subprocess, sys
from pathlib import Path
root=Path(__file__).resolve().parent.parent
out=root/'results/r0-cost-probe-20261009'
out.mkdir(parents=True,exist_ok=True)
label,*command=sys.argv[1:]
assert not (out/(label+'.json')).exists(), 'unchanged job/evidence rerun forbidden'
manifest=json.loads((out/'source-manifest.json').read_text())
(out/(label+'-source-manifest.json')).write_text(json.dumps(manifest,indent=2)+'\n')
for name,digest in manifest['files'].items():
    assert hashlib.sha256((root/name).read_bytes()).hexdigest()==digest,name
units=subprocess.check_output(['systemctl','--user','list-units','--type=scope','--state=running','--no-legend','--plain'],text=True)
reservations=[]
for line in units.splitlines():
    unit=line.split()[0]
    if unit=='init.scope': continue
    props=subprocess.check_output(['systemctl','--user','show',unit,'-p','MemoryMax','-p','MemoryHigh','-p','MemoryCurrent','-p','MemorySwapMax'],text=True)
    values=dict(v.split('=',1) for v in props.splitlines())
    # Unit may have finished between enumeration and property read.
    if values['MemoryCurrent']=='[not set]': continue
    assert values['MemoryMax']!='infinity', (unit,values)
    reservations.append(dict(unit=unit,**values))
cap=6*2**30
assert sum(int(r['MemoryMax']) for r in reservations)+cap <= 50*2**30,reservations
(out/(label+'-reservations.json')).write_text(json.dumps(dict(active=reservations,new_memory_max=cap,safe_limit=50*2**30,meminfo=Path('/proc/meminfo').read_text()),indent=2)+'\n')
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/home/dombarker/.local/share/solana/install/releases/3.1.13/solana-release/bin:'+os.environ['PATH'],
    CARGO_BUILD_JOBS='2',ASPIS_SOURCE_REVISION=manifest['source_revision'],
    R0_E2E_FIXTURE_DIR=str(out/'fixtures'), CARGO_TARGET_DIR=os.environ.get('R0_TARGET_DIR',str(root/'target')))
args=['systemd-run','--user','--scope','--unit=aspis-r0-p1-prime-'+label,'-p','MemoryHigh=4G','-p','MemoryMax=6G','-p','MemorySwapMax=0',
    'env']+[k+'='+env[k] for k in ['PATH','CARGO_BUILD_JOBS','CARGO_TARGET_DIR','ASPIS_SOURCE_REVISION','R0_E2E_FIXTURE_DIR']]+[
    'python3','scripts/v8_state_only_cu_record.py',str(out/label)]+command
sys.exit(subprocess.call(args,cwd=root))
