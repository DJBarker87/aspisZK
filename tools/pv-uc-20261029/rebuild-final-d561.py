"""Rebuild the changed client/audit copy; verify retained fixture and ELF identities."""
from pathlib import Path
import hashlib,json,subprocess,os,re
H=Path('/home/dombarker/project-offloads/codex-pv-uc-20261029');C=H/'src/tools/r1-cost-probe';O=H/'final-gates/d561-final';O.mkdir(exist_ok=False)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins=json.loads((H/'final-audit-expected.json').read_text())
# Stage only the approved literal edit; check every other recorded source.
for name,want in pins['production_sources'].items():
 p=H/'src'/name
 if name.endswith('user_client.rs'):
  assert hashlib.sha256(p.read_bytes().replace(b'b[i]>>4u32',b'b[i]>>4')).hexdigest()==want
 elif name.endswith('user_client/membership.rs'):
  assert hashlib.sha256(p.read_bytes().replace(b'1<<20u32',b'1<<20').replace(b'index>>=1u32;',b'index>>=1;')).hexdigest()==want
 elif name.endswith('user_client/wallet.rs'):
  assert hashlib.sha256(p.read_bytes().replace(b'<<32u32)',b'<<32)')).hexdigest()==want
 else:assert sha(p)==want,(name,'unexpected source change')
e=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_TARGET_DIR=str(H/'native-target'),RUSTFLAGS='--cfg getrandom_backend="linux_raw" --check-cfg=cfg(getrandom_backend,values("linux_raw")) -C link-arg=-Wl,--threads=4')
c=['taskset','--cpu-list','0-3','cargo','+1.94.1','build','--profile','client','--locked','--offline','-j','4','--features','r1p-check,aspis-r1-cost-probe/ct-host-prover','--bin','user_client']
print('EXPECTED WORK: incremental optimized client compilation/link only; differential proof generation is a separate scope',flush=True)
subprocess.run(c,cwd=C,env=e,check=True)
audit=['taskset','--cpu-list','0-3','cargo','+1.94.1','build','--manifest-path',str(H/'audit-src/Cargo.toml'),'--profile','client','--locked','--offline','-j','4','--features','r1p-check,aspis-r1-cost-probe/ct-host-prover','--bin','pv-uc-user-audit']
# Audit root/plan retain their exact earlier bytes and absolute wallet module path.
old=json.loads((H/'final-gates/audit-build-fixed.json').read_text())
for row in old['source_copies']:
 for part in ['root','plan']:
  assert sha(H/'audit-src'/(row['side']+('-plan' if part=='plan' else '')+'.rs'))==row['audit_'+part+'_sha256']
# Refresh only the user audit root by the original generation recipe.
root=C/'src/bin/user_client.rs'
root_s=re.sub(r'#\[path="([^\"]+)"\]',lambda m:'#[path='+json.dumps(str(H/'audit-src/user-plan.rs' if m[1]=='user_client/plan.rs' else root.parent/m[1]))+']',root.read_text())
root_s+='\n#[path='+json.dumps(str(H/'audit_export.rs'))+']\nmod audit_export;\n'
assert root_s.encode()==(H/'audit-src/user.rs').read_bytes().replace(b'b[i]>>4',b'b[i]>>4u32')
(H/'audit-src/user.rs').write_text(root_s)
subprocess.run(audit,env=e,check=True)
for name in ['devnet_spend','user_fixture_inputs']:
 assert sha(H/'native-target/client'/name)==pins['client_pins'][name]['sha256']
assert sha(H/'native-target/client/pv-uc-fixture-audit')==pins['audit_pins']['pv-uc-fixture-audit']
elves={}
for mode,want in pins['elf_pins'].items():
 p=H/'final-gates'/('elf-'+mode)/('aspis_pool.so' if mode=='pool' else 'aspis_r1_cost_probe_program.so')
 assert sha(p)==want,(mode,'ELF identity failed')
 elves[mode]=dict(path=str(p),sha256=want,byte_identical=True,method='retained ELF hash; client-only source cannot reach SBF roots, N75137/38/39 build evidence reused')
binaries={p.name:dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size) for p in [H/'native-target/client'/n for n in ['user_client','devnet_spend','pv-uc-user-audit','pv-uc-fixture-audit']]}
(O/'build.json').write_text(json.dumps(dict(command=c,audit_command=audit,environment={k:e[k] for k in ['RUSTFLAGS','CARGO_TARGET_DIR']},toolchain=subprocess.check_output(['rustc','+1.94.1','-Vv'],env=e,text=True),binaries=binaries,elf_identity=elves,fixture_unchanged=True),indent=2)+'\n')
print(json.dumps(dict(binaries=binaries,elf_identity=elves)),flush=True)
