"""Rebuild the changed client/audit copy; verify retained fixture and ELF identities."""
from pathlib import Path
import hashlib,json,subprocess,os,re
H=Path('/home/dombarker/project-offloads/codex-pv-uc-20261029');C=H/'src/tools/r1-cost-probe';O=H/'final-gates/ready';O.mkdir(exist_ok=False)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins=json.loads((H/'final-audit-expected.json').read_text())
# Stage only the approved literal edit; check every other recorded source.
normalizers={
 'user_client.rs':lambda b:b.split(b'\n// Extraction boundaries retain actual operands')[0].replace(b'let rendered=render_json(&plan::run(&q)?);print_json(rendered)',b'println!("{}",plan::run(&q)?)').replace(b'b[i]>>4u32',b'b[i]>>4').replace(b'parse_request(&s)?',b'serde_json::from_str(&s).map_err(err)?'),
 'user_client/wallet.rs':lambda b:wallet_original(b),
 'user_client/membership.rs':lambda b:b.replace(b'1<<20u32',b'1<<20').replace(b'index>>=1u32;',b'index>>=1;').replace(b'crate::parent_capacity(nodes.len())',b'nodes.len().div_ceil(2).max(1)').replace(b'match_count',b'matches'),
}
def wallet_original(b):
 new=b""" let mut channel=crate::wallet_open_channel(crate::wallet_fd_path(fd))?;
 let record=crate::wallet_read_record(&mut channel)?;
 let decoded=decode_wallet_record(&record);
 ensure!(canonical(&decoded),\"noncanonical wallet field\");Ok(decoded)"""
 old=b""" let mut channel=std::fs::File::open(format!(\"/proc/self/fd/{fd}\")).map_err(err)?;
 let mut record=[0u8;WIDTH];channel.read_exact(&mut record).map_err(err)?;
 let mut tail=[0u8;1];ensure!(channel.read(&mut tail).map_err(err)?==0,\"extra wallet bytes\");
 let wallet=decode_wallet_record(&record);
 ensure!(canonical(&wallet),\"noncanonical wallet field\");Ok(wallet)"""
 assert b.count(new)==1
 return b.replace(new,old).replace(b'<<32u32)',b'<<32)')
def json_original(b):
 for name in ['p','proof_account','marker','lanes[output_lane as usize]','page','key','public','checkpoint']:
  b=b.replace(('crate::pubkey_text('+name+')').encode(),(name+'.to_string()').encode())
 for v in ['String','Array','Bool','Number','Object']:b=b.replace(('crate::json_'+v.lower()+'(').encode(),('Value::'+v+'(').encode())
 b=b.replace(b'crate::public_lanes(pool,master)',b'(0..8).map(|i|pool_v1_pair_forest_lane_address(&pool,&master,i).unwrap().0).collect()')
 return b.replace(b'crate::json_into_array(stage1_accounts)?',b'match stage1_accounts { Value::Array(a)=>a,_=>return Err(anyhow!("publication shape")) }')
normalizers['user_client/plan.rs']=json_original;normalizers['user_client/accounts.rs']=json_original
sources={}
for name,want in pins['production_sources'].items():
 p=H/'src'/name;raw=p.read_bytes();relative=name.removeprefix('tools/r1-cost-probe/src/bin/')
 restored=normalizers.get(relative,lambda b:b)(raw)
 assert hashlib.sha256(restored).hexdigest()==want,(name,'unexpected source change beyond registered boundaries')
 sources[name]=dict(sha256=sha(p),normalized_to_original_sha256=want)
e=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_TARGET_DIR=str(H/'native-target'),RUSTFLAGS='--cfg getrandom_backend="linux_raw" --check-cfg=cfg(getrandom_backend,values("linux_raw")) -C link-arg=-Wl,--threads=4')
c=['taskset','--cpu-list','0-3','cargo','+1.94.1','build','--profile','client','--locked','--offline','-j','4','--features','r1p-check,aspis-r1-cost-probe/ct-host-prover','--bin','user_client']
print('EXPECTED WORK: incremental optimized client compilation/link only; differential proof generation is a separate scope',flush=True)
subprocess.run(c,cwd=C,env=e,check=True)
audit=['taskset','--cpu-list','0-3','cargo','+1.94.1','build','--manifest-path',str(H/'audit-src/Cargo.toml'),'--profile','client','--locked','--offline','-j','4','--features','r1p-check,aspis-r1-cost-probe/ct-host-prover','--bin','pv-uc-user-audit']
# Fixture audit inputs stay exactly pinned; user audit inputs are regenerated
# by the same single additive capture recipe from final production sources.
old=json.loads((H/'final-gates/audit-build-fixed.json').read_text())
for row in old['source_copies']:
 if row['side']!='fixture':continue
 for part in ['root','plan']:
  assert sha(H/'audit-src'/(row['side']+('-plan' if part=='plan' else '')+'.rs'))==row['audit_'+part+'_sha256']
root=C/'src/bin/user_client.rs';plan=C/'src/bin/user_client/plan.rs'
plan_s=re.sub(r'#\[path="([^\"]+)"\]',lambda m:'#[path='+json.dumps(str(plan.parent/m[1]))+']',plan.read_text())
needle=' let result=RealR1_client::prove_for_proof_accounts';assert plan_s.count(needle)==1
plan_s=plan_s.replace(needle,' super::audit_export::capture(dir,&compiled);\n'+needle)
(H/'audit-src/user-plan.rs').write_text(plan_s)
root_s=re.sub(r'#\[path="([^\"]+)"\]',lambda m:'#[path='+json.dumps(str(H/'audit-src/user-plan.rs' if m[1]=='user_client/plan.rs' else root.parent/m[1]))+']',root.read_text())
root_s+='\n#[path='+json.dumps(str(H/'audit_export.rs'))+']\nmod audit_export;\n'
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
(O/'build.json').write_text(json.dumps(dict(source_binding=sources,audit_user_root_sha256=sha(H/"audit-src/user.rs"),audit_user_plan_sha256=sha(H/"audit-src/user-plan.rs"),command=c,audit_command=audit,environment={k:e[k] for k in ['RUSTFLAGS','CARGO_TARGET_DIR']},toolchain=subprocess.check_output(['rustc','+1.94.1','-Vv'],env=e,text=True),binaries=binaries,elf_identity=elves,fixture_unchanged=True),indent=2)+'\n')
print(json.dumps(dict(binaries=binaries,elf_identity=elves)),flush=True)
