#!/usr/bin/env python3
"""Collect formal receipts and verify recovery of the exported dependency cache."""
import argparse,hashlib,json,shutil,subprocess
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args();out=a.output
assert not out.exists();out.mkdir();parent=Path('/home/dombarker/project-offloads')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def copy(src,n):
    assert src.is_file()and'keypair'not in str(src);dst=out/n;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src,dst)
stage=parent/'aspis-r31-inverse-20260928-b';m=json.loads((stage/'r18-stage.json').read_text())
for n,h in m['files'].items():assert sha(stage/n)==h,n
copy(stage/'r18-stage.json','source-manifest.json')
for letter in 'abcd':
    folder=parent/f'aspis-r32-lean-20260928-{letter}'
    for f in folder.glob('*'):
        if f.suffix in['.json','.log']:copy(f,'lean-'+letter+'/'+f.name)
    for f in (folder/'workspace').glob('*'):
        if f.is_file():copy(f,'lean-'+letter+'/workspace/'+f.name)
old=parent/'aspis-pool-single-decode-20260825-a3/AspisFormal/.lake/packages/mathlib'
recovered=parent/'aspis-pool-prepared-append-20260825-a4/AspisFormal/.lake/packages/mathlib'
commands=[['git','--git-dir='+str(recovered/'.git'),'--work-tree='+str(old),'diff','--exit-code','--stat'],['diff','-qr',str(old/'.lake'),str(recovered/'.lake')]]
checks=[]
for i,cmd in enumerate(commands):
    with(out/f'cache-recovery-{i}.log').open('w')as f:r=subprocess.run(['/usr/bin/time','-v',*cmd],stdout=f,stderr=subprocess.STDOUT)
    checks.append({'command':cmd,'exit':r.returncode});assert r.returncode==0
rev=subprocess.check_output(['git','-C',str(recovered),'rev-parse','HEAD'],text=True).strip()
assert rev=='81a5d257c8e410db227a6665ed08f64fea08e997'
(out/'cache-recovery.json').write_text(json.dumps({'retained':str(old),'recovered':str(recovered),'mathlib_revision':rev,'checks':checks,'new_runner_uses_dependency_free_workspace':True,'dependency_cache_rebuilt':False},indent=2)+'\n')
(out/'receipt.json').write_text(json.dumps({'parent_revision':'66727edcc16549a5dd251dc1eca3d2d2e2c57ad5','source_manifest_sha256':sha(stage/'r18-stage.json'),'source_pins':len(m['files']),'formal_final':str(parent/'aspis-r32-lean-20260928-d'),'new_lean_declarations':13,'scope':{'MemoryHigh':'3G','MemoryMax':'5G','MemorySwapMax':0,'TasksMax':128},'determinant_total_degree_bound':1355,'nonzero_polynomial_proved':True,'source_oracle_probability_bound_proved':False,'full_privacy':False,'verifier_changed':False},indent=2)+'\n')
(out/'MANIFEST.json').write_text(json.dumps({str(f.relative_to(out)):sha(f)for f in sorted(out.rglob('*'))if f.is_file()},indent=2)+'\n')
print(json.dumps({'artifacts':len(json.loads((out/'MANIFEST.json').read_text())),'source_pins':len(m['files'])}))
