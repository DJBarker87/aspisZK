"""Rebuild the changed client/audit copy; verify retained fixture and ELF identities."""
from pathlib import Path
import hashlib,json,subprocess,os,re
H=Path('/home/dombarker/project-offloads/codex-pv-uc-20261029');C=H/'src/tools/r1-cost-probe';O=H/'final-gates/uc5-final';O.mkdir(exist_ok=False)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins=json.loads((H/'final-audit-expected.json').read_text())
e=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_TARGET_DIR=str(H/'native-target'),RUSTFLAGS='--cfg getrandom_backend="linux_raw" --check-cfg=cfg(getrandom_backend,values("linux_raw")) -C link-arg=-Wl,--threads=4')
c=['taskset','--cpu-list','0-3','cargo','+1.94.1','build','--profile','client','--locked','--offline','-j','4','--features','r1p-check,aspis-r1-cost-probe/ct-host-prover','--bin','user_client']
print('EXPECTED WORK: incremental optimized client compilation/link only; differential proof generation is a separate scope',flush=True)
subprocess.run(c,cwd=C,env=e,check=True)
# Client-only changes cannot reach release roots; recheck all retained ELF bytes.
for name in ['devnet_spend','user_fixture_inputs']:
 assert sha(H/'native-target/client'/name)==pins['client_pins'][name]['sha256']
elves={}
for mode,want in pins['elf_pins'].items():
 p=H/'final-gates'/('elf-'+mode)/('aspis_pool.so' if mode=='pool' else 'aspis_r1_cost_probe_program.so')
 assert sha(p)==want
 elves[mode]=dict(sha256=want,method='retained byte identity; client-only source, earlier fresh SBF builds reused')
binaries={p.name:dict(sha256=sha(p),bytes=p.stat().st_size) for p in [H/'native-target/client'/n for n in ['user_client','devnet_spend']]}
(O/'build.json').write_text(json.dumps(dict(command=c,binaries=binaries,elf_identity=elves,fixture_unchanged=True,sources={str(p.relative_to(H/'src')):sha(p) for p in (C/'src/bin').rglob('user_client*.rs')}),indent=2)+'\n')
print(json.dumps(dict(binaries=binaries,elf_identity=elves)))
