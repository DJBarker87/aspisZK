from pathlib import Path
import json,hashlib,tarfile,tomllib
root=Path('/home/dombarker/project-offloads/root-runtime-meter-count-v2-20261019'); dst=root/'runtime-source-pins';dst.mkdir(exist_ok=True)
registry=Path('/home/dombarker/.cargo/registry'); kind='index.crates.io-1949cf8c6b5b557f';sha=lambda b:hashlib.sha256(b).hexdigest()
adopt=Path('/home/dombarker/project-offloads/codex-r1-format-adopt-20261019'); lock=adopt/'src/tools/r1-cost-probe-adopt-driver/Cargo.lock';packages=tomllib.loads(lock.read_text())['package']; out={'scope':'Measured adoption driver runtime only; deployed cluster/runtime configuration and formal runtime trace refinement OPEN','lock':{'path':str(lock),'sha256':sha(lock.read_bytes())},'packages':[],'artifacts':[]}
items={
'solana-program-runtime':('4.2.1',{'src/execution_budget.rs':[(20,32),(190,215)],'src/invoke_context.rs':[(190,225),(250,268)]}),
'solana-syscalls':('4.2.1',{'src/lib.rs':[(185,218),(835,940),(2535,2610)]}),
'solana-compute-budget-instruction':('4.2.1',{'src/compute_budget_instruction_details.rs':[(110,140)]}),
'solana-pubkey':('4.2.1',{'src/lib.rs':[(1,80)]}),
'solana-address':('2.6.1',{'src/syscalls.rs':[(385,440)]})}
for name,(version,files) in items.items():
 p=next(x for x in packages if x['name']==name and x['version']==version); archive=registry/'cache'/kind/f'{name}-{version}.crate';assert sha(archive.read_bytes())==p['checksum'],name
 rec={'name':name,'version':version,'cargo_lock_checksum':p['checksum'],'cached_crate_path':str(archive),'cached_crate_sha256_verified':True,'files':[]}
 with tarfile.open(archive) as tar:
  for path,ranges in files.items():
   file=registry/'src'/kind/f'{name}-{version}'/path; data=file.read_bytes();member=tar.extractfile(f'{name}-{version}/{path}');assert member and member.read()==data,(name,path)
   fragments=[];lines=data.decode().splitlines()
   for a,b in ranges:
    rel=Path(name)/f'{Path(path).name}.L{a}-L{b}.txt'; target=dst/rel;target.parent.mkdir(parents=True,exist_ok=True);target.write_text('\n'.join(f'{i}: {lines[i-1]}'.rstrip() for i in range(a,min(b,len(lines))+1))+'\n');fragments.append({'lines':[a,b],'path':str(rel),'sha256':sha(target.read_bytes())})
   rec['files'].append({'registry_path':str(file),'crate_member':f'{name}-{version}/{path}','sha256':sha(data),'archive_member_equal':True,'fragments':fragments})
 out['packages'].append(rec)
for rel,expected in [('artifacts/verifier/aspis_r1_cost_probe_program.so','8cf8d84ed0fe340a190b4f40a9f953f0e0523370299ba3ec8bbed9d65b88ace3'),('artifacts/pool/aspis_pool.so','121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548')]:
 f=adopt/rel;actual=sha(f.read_bytes());assert actual==expected,rel;out['artifacts'].append({'path':str(f),'sha256':actual,'bytes':f.stat().st_size,'copied':False})
(dst/'pins.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'packages':len(out['packages']),'artifacts':out['artifacts']}))
