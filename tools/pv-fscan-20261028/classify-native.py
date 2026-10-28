"""Recompile unchanged finite library fixtures on deployed rustc, no Kani."""
from pathlib import Path
import os,subprocess,json,sys,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-fscan-20261028');suite=sys.argv[1];S=D/'classification-inputs';O=D/('classify-native-'+suite);O.mkdir(exist_ok=True)
fixtures={
'std-extra':('classify-std-fixture.rs',False),
'join':('v178.rs',False), 'append':('v182.rs',False),
'drop':('drop-u32.rs',False),'reserve':('reserve-native.rs',False),
'pop':('pop-move-world.rs',False),'pop-zst':('pop-zst-world.rs',False),
'array':('array-owned-reference.rs',True),
'zeroize':('zeroize-native.rs',False),'zeroize-drop':('zeroize-drop.rs',False)}
f,test=fixtures[suite];env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:'+os.environ['PATH'],RUSTUP_TOOLCHAIN='1.94.1')
rustc='/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/bin/rustc'
commands=[]
def run(cmd):
 commands.append(cmd);r=subprocess.run(cmd,env=env,capture_output=True,text=True);print(r.stdout,flush=True);print(r.stderr,flush=True)
 if r.returncode:raise SystemExit(r.returncode)
run([rustc,'-vV']);cmd=[rustc,'-Copt-level=3','-Cdebug-assertions=false','-Coverflow-checks=false','-Cpanic=unwind','--edition=2021',str(S/f),'-o',str(O/'check')]
features={}
if suite=='reserve':env['RUSTC_BOOTSTRAP']='1' # try_reserve_kind only: inspect complete allocation error kind
if suite.startswith('zeroize'):
 z=Path('/home/dombarker/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/zeroize-1.9.0/src/lib.rs')
 # Cargo resolves the deployed zeroize feature graph including derive; never select an arbitrary cached rlib.
 P=D/'classification-zeroize';P.mkdir(exist_ok=True)
 manifest='''[package]\nname="pv-fscan-zeroize-deployed"\nversion="0.0.0"\nedition="2021"\n[workspace]\n[lib]\npath="../std-probe.rs"\n[dependencies]\nzeroize={version="=1.9.0",features=["alloc","zeroize_derive"]}\n'''
 (P/'Cargo.toml').write_text(manifest);env['CARGO_TARGET_DIR']=str(D/'classification-target')
 cargo=['cargo','build','--manifest-path',str(P/'Cargo.toml'),'--release','-j','4','--message-format=json']
 commands.append(cargo);r=subprocess.run(cargo,env=env,capture_output=True,text=True);(O/'cargo-artifacts.jsonl').write_text(r.stdout);print(r.stderr,flush=True)
 if r.returncode:raise SystemExit(r.returncode)
 arts=[json.loads(l) for l in r.stdout.splitlines()];a=next(a for a in arts if a.get('reason')=='compiler-artifact' and a['target']['name']=='zeroize');lib=next(f for f in a['filenames'] if f.endswith('.rlib'));features=a['features'];cmd+=['--extern','zeroize='+lib,'-L','dependency='+str(Path(lib).parent)]
 meta=subprocess.check_output(['cargo','metadata','--manifest-path',str(P/'Cargo.toml'),'--format-version','1'],env=env,text=True);(O/'metadata.json').write_text(meta)
if test:cmd+=['--test']
(O/'inputs.json').write_text(json.dumps(dict(source_file=f,sha256=hashlib.sha256((S/f).read_bytes()).hexdigest(),features=features,profile={'opt_level':3,'debug_assertions':False,'overflow_checks':False,'panic':'unwind'},toolchain='1.94.1'),indent=2))
(O/'command.json').write_text(json.dumps(commands+[cmd,[str(O/'check')]],indent=2));run(cmd);run([str(O/'check')]+(['--nocapture','--test-threads=1'] if test else []))
print('FINITE VALIDATION ONLY; original domains/world and compiler realization residuals retained')
