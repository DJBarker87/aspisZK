from pathlib import Path
import json,hashlib,subprocess
w=Path('/home/dombarker/project-offloads/aspis-r1-cu-savings-20261019');v=w/'verifier.rs'
for name in ['clean','sbf']:(w/name/'crates/aspis-r1-cost-probe/src/verifier.rs').write_bytes(v.read_bytes())
p=w/'injections/crates/aspis-r1-cost-probe/src/verifier.rs';s=p.read_text()
# Freeze the baseline helper for the old side; preserve its existing test fault hook.
a=s.index('fn prepared_claim<');b=s.index('\nimpl Prepared',a)
s+='\n'+s[a:b].replace('fn prepared_claim<','fn migration_old_prepared_claim<',1)
s=s.replace('inactive:E,gamma:E,kappa:E)->Result<E,Error> {\n        let g=powers::<29>(gamma);let k=powers::<7>(kappa);','inactive:E,g:&[E;29],kappa:E)->Result<E,Error> {\n        let k=powers::<7>(kappa);',1)
s=s.replace("pub fn new<H:Digest32>(sem:&crate::r1_semantic::Verified<H>,v:&View<'_>,hash:H)->Result<Box<Self>,Error> {","pub fn new<H:Digest32>(sem:&crate::r1_semantic::Verified<H>,v:&View<'_>,hash:H,g:&mut [E;29])->Result<Box<Self>,Error> {",1)
s=s.replace('let claim=prepared_claim(sem,v.y1,v.inactive,gamma,kappa)?;','*g=powers::<29>(gamma);\n        let claim=prepared_claim(sem,v.y1,v.inactive,g,kappa)?;',1)
s=s.replace("fn tx1_prepare<H:Digest32>(public:Public<'_>,v:&View<'_>,hash:H,obs:Observer)","fn tx1_prepare<H:Digest32>(public:Public<'_>,v:&View<'_>,hash:H,obs:Observer,g:&mut [E;29])")
s=s.replace('let p=Prepared::new(&sem,v,hash)?;','let p=Prepared::new(&sem,v,hash,g)?;',1)
s=s.replace('let (_semantic_claims,p)=tx1_prepare(public,&v,hash,obs)?;let mut a=Accumulator::new(v.variant)?;let g=powers::<29>(p.gamma);mark(obs,Phase::Prepare);','let mut g=[E::ZERO;29];\n    let (_semantic_claims,p)=tx1_prepare(public,&v,hash,obs,&mut g)?;let a=Accumulator::new(v.variant)?;mark(obs,Phase::Prepare);',1)
s=s.replace('let p=Prepared::new(&sem,&v,hash)?;','let p=Prepared::decision1h_old_new(&sem,&v,hash)?;')
s=s.replace('let claim=prepared_claim(sem,v.y1,v.inactive,gamma,kappa)?;','let claim=migration_old_prepared_claim(sem,v.y1,v.inactive,gamma,kappa)?;')
p.write_text(s)
p=w/'injections/crates/aspis-r1-cost-probe/src/decision1h_prepared_migration_tests.rs';s=p.read_text().replace('Prepared::new(&sem,&view,RecordedSha)','Prepared::new(&sem,&view,RecordedSha,&mut [E::ZERO;29])');p.write_text(s)
# Generic strict audit: same ELF parser and warning classification as accepted audit.
s=(w/'r1-strict-stack-audit.py').read_text().split('# Pin all producing external-tool outputs')[0]
s=s.replace("W=Path(__file__).resolve().parent","W=Path(sys.argv[1]).resolve()")
s=s.replace('assert numeric\n','')
s+='''\nsurvivors=[n for n in numeric if n['classification']!='UNREACHABLE_ABSENT_FROM_LINKED_ELF']\nsurviving_overwrites=[o for o in overwrites if o['classification']!='UNREACHABLE_ABSENT_FROM_LINKED_ELF']\nreport={'gate_pass':not(survivors or surviving_overwrites or unparsed),'linked_sha256':linked['sha256'],'stripped_sha256':stripped['sha256'],'numeric_diagnostics':numeric,'overwrite_diagnostics':overwrites,'unparsed':unparsed,'actual_tx1':actual,'call_paths':source_paths,'all_direct_call_edges':call_edges,'surviving_oversized':survivors,'surviving_overwrites':surviving_overwrites,'policy':'Every surviving oversized frame fails conservatively; exact absence from full linked ELF, symbols and relocations required for waiver.'}\n(W/'stack-audit.json').write_text(json.dumps(report,indent=2)+'\\n');print(json.dumps({k:report[k] for k in ['gate_pass','linked_sha256','stripped_sha256','surviving_oversized','surviving_overwrites','unparsed']}));assert report['gate_pass']\n'''
(w/'strict-stack.py').write_text(s)
rev='3ab4faf7f';base=Path('/home/dombarker/project-offloads/aspis-r1-worker-b-1h-native-20261019')
env={'PATH':'/home/dombarker/.cargo/bin:/usr/bin:/bin','RUSTUP_TOOLCHAIN':'stable','CARGO_BUILD_JOBS':'1','CARGO_NET_OFFLINE':'true','CARGO_TARGET_DIR':str(base/'cargo-target')}
cargo=['/home/dombarker/.cargo/bin/cargo'];common=['--verbose','--release','--locked','--offline','-j1']
commands=[('codec',cargo+['run']+common+['-p','aspis-statement','--features','r0,pool-v1-kernel','--example','j1_terminal_codec_trace'],'clean',['r0','pool-v1-kernel']),('counter',cargo+['run']+common+['--manifest-path','tools/r1-hash-input-counter/Cargo.toml','--',str(base/'fixtures/r1-s2-proof.bin'),str(base/'fixtures/r1-s2-public-asf8.bin'),str(w/'candidate1-ordered.json'),rev],'clean',['private-leaf-salts']),('checkpoint',cargo+['test']+common+['-p','aspis-r1-cost-probe-program','--features','pool-adapter,private-leaf-salts','--lib','r1_pool_adapter::checkpoint_tests::','--','--test-threads=1'],'clean',['pool-adapter','private-leaf-salts'])]
for detail in [False,True]:
 f='private-leaf-salts,optimized-terminal'+(',detail-phases' if detail else '')
 commands.append(('injections-'+('detail' if detail else 'default'),cargo+['test']+common+['-p','aspis-r1-cost-probe','--features',f,'--lib','decision1h','--','--nocapture','--test-threads=1'],'injections',f.split(',')))
for label,cmd,tree,features in commands:
 e=dict(env)
 if tree=='injections':e['CARGO_TARGET_DIR']='/home/dombarker/project-offloads/aspis-r1-worker-b-1h-injection-20261019/cargo-target'
 plan={'command':cmd,'cwd':str(w/tree),'source_revision':rev,'features':features,'out':str(w/'runs'/('c1-'+label)),'env':e,'expected_time':'optimized native compilation and saved-fixture verification; no proof generation'}
 (w/(label+'.json')).write_text(json.dumps(plan,indent=2)+'\n')
manifest={str(p.relative_to(w)):hashlib.sha256(p.read_bytes()).hexdigest() for name in ['clean','injections','sbf'] for p in (w/name).rglob('*') if p.is_file()}
(w/'candidate1-inputs.json').write_text(json.dumps({'revision':rev,'files':manifest},indent=2)+'\n')
