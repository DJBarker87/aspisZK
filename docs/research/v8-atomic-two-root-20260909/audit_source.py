#!/usr/bin/env python3
"""Locally reconstruct the four permitted task-copy overlays and compare bytes."""
import hashlib,json,pathlib,shutil,subprocess,tempfile
HERE=pathlib.Path(__file__).resolve().parent
ROOT=HERE.parents[2]
BASE='4aaa61e679189b2cf76bfc25c2e3ff8d5c76341e'
lock=json.loads((HERE/'evidence/build-inputs.json').read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
changed=[p for p,h in lock['source_files'].items() if sha(ROOT/p)!=h]
assert set(changed)=={
 'crates/aspis-statement/src/pool_v1/tag73_pair_forest_profile.rs',
 'programs/aspis-verifier/src/lib.rs','programs/aspis-verifier/src/v7_pair_forest_dispatch.rs',
 'results/v7-pair-forest-combined-rejection-litesvm-20260828/harness/src/main.rs'}
subprocess.run(['git','diff','--exit-code',BASE,'--','crates','programs','Cargo.toml','Cargo.lock',
 'docs/research/v8-no-work-100-20260907','results/v7-pair-forest-combined-rejection-litesvm-20260828'],cwd=ROOT,check=True,stdout=subprocess.DEVNULL)
with tempfile.TemporaryDirectory(prefix='aspis-atomic-source-audit-') as d:
    rt=pathlib.Path(d).resolve()
    for name in changed:
        (rt/name).parent.mkdir(parents=True,exist_ok=True);shutil.copy2(ROOT/name,rt/name)
    for patch in ['complete-integration','complete-matched-driver','pool-zero-driver','token-control-driver']:
        subprocess.run(['git','apply','--recount','--unidiff-zero',str(HERE.parent/f'v8-no-work-100-20260907/experiments/{patch}.patch')],cwd=rt,check=True)
    installer=rt/'docs/research/v8-atomic-two-root-20260909/install_driver.py'
    installer.parent.mkdir(parents=True,exist_ok=True)
    installer.write_text((HERE/'install_driver.py').read_text().replace('/home/dombarker/project-offloads/aspis-v8-atomic-two-root-20260909',str(rt)))
    subprocess.run(['python3',str(installer)],check=True,stdout=subprocess.DEVNULL)
    for name in changed:assert sha(rt/name)==lock['source_files'][name],name
print(json.dumps({'base':BASE,'checked_source_files':len(lock['source_files']),'reconstructed_overlay_files':changed,'status':'exact-byte-match'},indent=2))
