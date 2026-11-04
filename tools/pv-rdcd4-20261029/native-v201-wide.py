"""Original finite fixtures rebound to frozen source paths, deployed graph and rustc.
All additional helpers/tests live outside crates/ and programs/.
"""
from pathlib import Path
import json,subprocess,sys,os,hashlib,ast,shutil
D=Path('/home/dombarker/project-offloads/codex-pv-rdcd4-20261029');S=Path('/home/dombarker/project-offloads/codex-pv-fscan-20261028/src');suite=sys.argv[1];O=D/('classify-project-'+suite);O.mkdir(exist_ok=True);P=D/'classification-project-fixture';P.mkdir(exist_ok=True)
bundle=json.loads(Path('/home/dombarker/project-offloads/codex-pv-rdcd-20261028/project-native-inputs.json').read_text());records=[]
def input_file(key):
 v=bundle[key];records.append(dict(path=key,sha256=v['sha256']));return v['text']
if suite=='statement-eq':
 source=input_file('tools/pv-rdcd-20261028/native-leaves.rs');test=True
elif suite=='focused-leaves':
 source=input_file('tools/pv-rdcd-20261028/native-leaves.rs');test=True
elif suite=='encoder':
 source=input_file('tools/pv-dlib-20261028/encoder-native.rs');(P/'owned-encoder.rs').write_text(input_file('tools/pv-dlib-20261028/owned-encoder.rs'));test=True
elif suite=='wide':
 bridge=input_file('tools/pv-relink-20261028/v195-bridge.rs')
 raw=(S/'crates/aspis-core/src/field/wide_exact.rs').read_bytes();(P/'wide_shadow.rs').write_bytes(raw+b'\n'+bridge.encode());records.append(dict(path='crates/aspis-core/src/field/wide_exact.rs',original_sha256=hashlib.sha256(raw).hexdigest(),prefix_identical=True,shadow='wide_shadow.rs',reason='original arbitrary raw-limb constructor requires private fields; same original prefix+helper route, outside crates'))
 # The only private pure super helper is copied verbatim from the frozen source.
 field=(S/'crates/aspis-core/src/field.rs').read_text();a=field.index('fn mul_by_r(');b=field.index('{',a);end=b+1;depth=1
 while depth:
  depth+=(field[end]=='{')-(field[end]=='}');end+=1
 helper=field[a:end];records.append(dict(path='crates/aspis-core/src/field.rs::mul_by_r',sha256=hashlib.sha256(helper.encode()).hexdigest(),body=helper))
 fixture=input_file('tools/pv-relink-20261028/v195.rs').replace('use aspis_core::field::pv_rl_bytes as native_and_reference;','use wide_shadow::pv_rl_checks::native_and_reference;')
 source='pub use aspis_core::field::{M31,CM31,P,QM31,ct};\n'+helper+'\nmod wide_shadow;\npub mod field {pub use crate::wide_shadow::WideExact;}\n'+fixture;test=False
elif suite=='circle':
 source=input_file('tools/pv-alib-20261027/sampler-owned-reference.rs');old='../../codex-pv-cblib-20261027/source/crates/aspis-r1-cost-probe/src/sampler.rs';source=source.replace(old,str(S/'crates/aspis-r1-cost-probe/src/sampler.rs'));test=True
elif suite=='sampler':
 source=input_file('tools/pv-batch2-20261027/sampler-native-batch2e.rs').replace('/home/dombarker/project-offloads/codex-pv-batch2-20261027/candidate/src/',str(S)+'/');test=False
elif suite=='weights':
 script=input_file('tools/pv-batch2-20261027/rowcheck-batch2c.py');tree=ast.parse(script);testcode=next(ast.literal_eval(n.value) for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='test' for t in n.targets));raw=(S/'crates/aspis-r1-cost-probe/src/host_weights.rs').read_bytes()
 (P/'host_weights_with_tests.rs').write_bytes(raw+testcode.encode());records.append(dict(path='crates/aspis-r1-cost-probe/src/host_weights.rs',original_sha256=hashlib.sha256(raw).hexdigest(),shadow_sha256=hashlib.sha256(raw+testcode.encode()).hexdigest(),prefix_identical=True))
 source='extern crate alloc;\npub use aspis_r1_cost_probe::{weights,transport,verifier};\n#[path="'+str(S/'crates/aspis-r1-cost-probe/src/prover_powers.rs')+'"] pub mod prover_powers;\nmod host_weights_with_tests;\n';test=True
elif suite=='rows':
 source=input_file('tools/pv-b3p6-20261028/lib.rs');test=True
 source=source.replace('pub mod reference226;','').replace('#[cfg(any(kani, test))]\nmod native226;','')
 for name in ['reference133.rs','owned133.rs']:(P/name).write_text(input_file('tools/pv-b3p6-20261028/'+name))
elif suite=='bytes':
 source=input_file('tools/pv-fscan-20261028/classify-bytes-fixture.rs');test=False
elif suite in ['arithmetic','multilinear']:
 key={'arithmetic':'evidence/pv-batch3-20261027/fidelity/main.rs','multilinear':'evidence/pv-batch3-20261027/fidelity222-native/main.rs'}[suite];source=input_file(key);test=False
elif suite=='sum':
 source=input_file('evidence/pv-op254-20261027/native/main.rs');test=False
 for key in bundle:
  if key.startswith('evidence/pv-op254-20261027/native/') and not key.endswith('/main.rs'):(P/Path(key).name).write_text(input_file(key))
elif suite=='leaves':
 source=input_file('tools/pv-fscan-20261028/classify-leaf-fixture.rs');test=False
 for name,key in [('compress','tools/pv-cb-20261026/step-proof/owned_compress.rs'),('boundary','tools/pv-cb3-20261026/reference_p6.rs'),('polynomial','tools/pv-cb3-20261026/reference_polynomial.rs')]:
  (P/(name+'.rs')).write_text(input_file(key))
else:raise ValueError(suite)
assert suite=='encoder'
source=source.replace('compare(base);compare(extension);','compare(|seed| aspis_core::field::WideExact::new(extension(seed),extension(seed.wrapping_mul(59).wrapping_add(23))));')
source=source.replace('128 dense native/reference comparisons; changed-write and sparse q[2] witnesses passed','64 WideExact dense native/reference comparisons; inherited small changed-write and sparse q[2] controls passed')
# Fail closed if current candidate source differs from the frozen native crate.
current=json.loads((D/'application-sources.json').read_text())
for row in current:
 if row['path'].startswith('crates/aspis-core/'):
  p=S/row['path'];actual=hashlib.sha256(p.read_bytes()).hexdigest()
  assert actual==row['sha256'],(str(p),actual,row['sha256'])
(P/'fixture.rs').write_text(source)
manifest='''[package]\nname="pv-fscan-deployed-project-fixture"\nversion="0.0.0"\nedition="2021"\n[workspace]\n[dependencies]\n'''
features={'aspis-prover':['ct-host-prover','insecure-spend-fixture','prover','r0'],'aspis-core':['ct-host-prover','r0'],'aspis-statement':['r0','pool-v1-kernel'],'aspis-r1-cost-probe':['ct-host-prover','default','private-leaf-salts','prover','r1p-check']}
for pkg,feats in features.items():manifest+=pkg+'={path="'+str(S/'crates'/pkg)+'",features='+json.dumps(feats)+'}\n'
manifest+='zeroize={version="=1.9.0",features=["alloc","zeroize_derive"]}\ngeneric-array={version="=0.14.7",features=["more_lengths","zeroize"]}\ntypenum={version="=1.20.1",features=["const-generics"]}\ndigest={version="=0.10.7",features=["alloc","const-oid","core-api","mac","oid","std"]}\ncrypto-common={version="=0.1.7",features=["getrandom","rand_core","std"]}\nsubtle={version="=2.6.1",features=["i128","std"]}\n'
manifest+=('[lib]\n' if test else '[[bin]]\nname="fixture"\n')+'path="fixture.rs"\n[profile.release]\noverflow-checks=false\ndebug-assertions=false\n'
manifest+='[features]\ndefault=["ct-host-prover"]\nct-host-prover=[]\n'
(P/'Cargo.toml').write_text(manifest);(O/'Cargo.toml.txt').write_text(manifest);(O/'fixture.rs.txt').write_text(source)
if not (P/'Cargo.lock').exists():
 lock=S/'tools/r1-cost-probe/Cargo.lock'
 assert lock.exists(),str(lock)
 shutil.copy2(lock,P/'Cargo.lock')
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:'+os.environ['PATH'],RUSTUP_TOOLCHAIN='1.94.1',CARGO_TARGET_DIR=str(D/'classification-target'),CARGO_BUILD_JOBS='4')
cmd=['cargo','test' if test else 'run','--manifest-path',str(P/'Cargo.toml'),'--release','--locked','-j','4']
if test:cmd+=['--lib','--']+(['statements'] if suite=='statement-eq' else [])+['--nocapture','--test-threads=1']
meta=subprocess.run(['cargo','metadata','--manifest-path',str(P/'Cargo.toml'),'--offline','--format-version','1'],env=env,capture_output=True,text=True);(O/'metadata.json').write_text(meta.stdout)
if meta.returncode:print(meta.stderr);sys.exit(meta.returncode)
m=json.loads(meta.stdout);nodes={p['id']:p for p in m['resolve']['nodes']};resolved=[dict(id=p['id'],name=p['name'],version=p['version'],features=nodes[p['id']]['features']) for p in m['packages']]
for pkg,want in features.items():
 actual=next(p['features'] for p in resolved if p['name']==pkg);assert sorted(actual)==sorted(want),(pkg,actual,want)
(O/'inputs.json').write_text(json.dumps(dict(command=cmd,env={k:v for k,v in env.items() if k.startswith(('RUST','CARGO'))},features=resolved,input_pins=records,profile='release opt3 debug_assertions=false overflow_checks=false panic=unwind',source_prefixes='No original source body modified; only external fixture path/import rebinding and same original tests appended to a shadow module outside crates/',expected_time='optimized compilation then '+suite+' finite differential; no proof aggregation/elimination'),indent=2))
print('expected time: optimized compilation then '+suite+' finite validation, no elimination',flush=True);r=subprocess.run(cmd,env=env);sys.exit(r.returncode)
