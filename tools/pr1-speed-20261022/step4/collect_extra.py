"""Collect final step-4 audit artifacts; never copy binaries, wallets or keys."""
from pathlib import Path
import hashlib,json,shutil,sys
r=Path(sys.argv[1]);out=Path(sys.argv[2]);out.mkdir(parents=True,exist_ok=True)
for name in ['elf-identities.json','public-work-two-run.json']:
 shutil.copy(r/name,out/name)
elf=json.loads((out/'elf-identities.json').read_text());assert len(elf)==3 and all(x['exit_status']==0 and x['byte_equal'] and x['sha256']==x['expected_sha256']for x in elf)
for p in (r/'receipts').glob('elf-step4c-*/receipt.json'):shutil.copytree(p.parent,out/'receipts'/p.parent.name,dirs_exist_ok=True)
for p in r.glob('reservation-elf-step4c-*.json'):shutil.copy(p,out/p.name)
meta={p.name:dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)for p in [r/'complete-bin',r/'challenge-bin',r/'public-work-trace-bin']}
(out/'host-binaries.json').write_text(json.dumps(meta,indent=2)+'\n')
for path in ['docs/research/v8-r0-zk-20261009/z4/z9e.rs','crates/aspis-r1-cost-probe/examples/ct_fixture_gate.rs','crates/aspis-r1-cost-probe/examples/pr1_challenges.rs','crates/aspis-r1-cost-probe/examples/public_work_trace.rs']:
 shutil.copy(r/path,out/(Path(path).name+'.txt'))
shutil.copy(r/'Cargo.lock',out/'root-Cargo.lock.txt')
