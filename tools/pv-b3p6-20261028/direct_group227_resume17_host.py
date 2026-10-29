"""One native scope per deployed module, isolated per-function translators.
Every invocation reads actual deployed lib/module files through a manifest-only
extraction driver. No source, LLBC, translator, or generated output is edited.
"""
from pathlib import Path
from run import H,run
import json,hashlib,subprocess,sys,shutil
kind,ident=sys.argv[1:3];assert kind in ('terminal','copy','field','poseidon','statement-copy','copy-methods','poseidon-methods','field-retry','poseidon-retry','statement-copy-retry');assert 73900<=int(ident)<=73929
R=H/'resume17';O=R/('direct-'+kind);O.mkdir(exist_ok=True)
basekind=kind.replace('-methods','').replace('-retry','')
if '--inside' not in sys.argv:
 label='N'+ident;retry=0
 while (R/label).exists():
  assert not (R/label/'receipt/receipt.json').exists(),'charged native ID cannot be reused'
  retry+=1;label='N'+ident+'-r'+str(retry)
 assert len(list(R.glob('N*/receipt/receipt.json')))<30
 raise SystemExit(run('resume17/'+label,['python3',str(Path(__file__)),kind,ident,'--inside'],'serial direct Charon/Aeneas per required '+kind+' function; optimized compilation and translation only',{'RUSTUP_TOOLCHAIN':'nightly-2026-06-01','CARGO_TARGET_DIR':str(H/'charon-target'),'CARGO_PROFILE_RELEASE_OPT_LEVEL':'3','CARGO_PROFILE_RELEASE_DEBUG_ASSERTIONS':'false','CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS':'false','PV_REV':(R/'revision').read_text().strip()}))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
c=Path('/home/dombarker/project-offloads/codex-pv-extract-20261027/charon');a=Path('/home/dombarker/project-offloads/codex-pv-cx-20261029/resume-ae1/pinned-tools/aeneas-ae1-2-fda587d2')
assert sha(c)=='daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8';assert sha(a)=='fda587d25a66604a973bbc2947a4416ba373b56dd8c98655991c1b6eaa240b68'
sources=json.loads((R/'deployed-source-pins.json').read_text())
for p,h in sources.items():assert sha(H/'source'/p)==h
module={'terminal':'host_terminal','copy':'host_copy_terminal','field':'field','poseidon':'state_only_poseidon','statement-copy':'pool_v1::pair_forest_copy_terminal'}[basekind]
driver={'terminal':'terminal','copy':'terminal','field':'field','poseidon':'poseidon','statement-copy':'poseidon'}[basekind]
manifest=H/('source/tools/pv-b3p6-20261028/v244-direct17-'+driver+'/Cargo.toml')
features={'terminal':'ct-host-prover','copy':'ct-host-prover','field':'r0,ct-host-prover','poseidon':'r0,pool-v1-kernel,aspis-core/ct-host-prover','statement-copy':'r0,pool-v1-kernel,aspis-core/ct-host-prover'}[basekind]
if not manifest.with_name('Cargo.lock').exists():shutil.copy2(manifest.parent.parent/'v244/Cargo.lock',manifest.with_name('Cargo.lock'))
meta=json.loads(subprocess.check_output(['/home/dombarker/.cargo/bin/cargo','+1.94.1','metadata','--offline','--format-version','1','--manifest-path',str(manifest),'--features',features],text=True))
pkgs={p['id']:p for p in meta['packages']};nodes=[dict(name=pkgs[n['id']]['name'],version=pkgs[n['id']]['version'],source=pkgs[n['id']]['source'],features=n['features'])for n in meta['resolve']['nodes']]
(O/'inputs.json').write_text(json.dumps(dict(kind=kind,scope='N'+ident,charon=str(c),charon_sha256=sha(c),aeneas=str(a),aeneas_sha256=sha(a),translator_identity='functionally identical rebuild (ae1-2)',sources=sources,manifest=str(manifest),manifest_sha256=sha(manifest),lock_sha256=sha(manifest.with_name('Cargo.lock')),nodes=nodes,features=features,lib_path=__import__('tomllib').loads(manifest.read_text())['lib']['path'],extractor_toolchain='nightly-2026-06-01',deployed_toolchain='1.94.1',release=dict(opt_level=3,debug_assertions=False,overflow_checks=False)),indent=2)+'\n')
roots=json.loads((R/'direct-roots.json').read_text())[basekind];results=[]
if kind.endswith('-methods'):roots=[n for n in roots if '::' in n]
for name in roots:
 out=O/name.replace('::','__');out.mkdir(exist_ok=True);assert not (out/'charon/receipt.json').exists(),'unchanged body trial cannot be repeated'
 llbc=out/'Deployed17.llbc';gen=out/'generated';gen.mkdir(exist_ok=True)
 cmd=['timeout','300','taskset','--cpu-list','0-3',str(c),'cargo','--preset','aeneas','--mir','optimized','--sysroot','default','--start-from','crate::'+module+'::'+(('_::'+name.split('::')[-1]) if '::' in name else name),'--include','crate::'+module,'--include','aspis_core::field','--dest-file',str(llbc),'--','--manifest-path',str(manifest),'--release','--locked','--offline','--lib','--jobs','4','--features',features]
 def invoke(stage,cmd):
  return subprocess.run(['python3',str(H/'capped.py'),str(out/stage),'isolated deployed '+kind+' '+name+' '+stage,'--',*cmd]).returncode
 status=invoke('charon',cmd);row=dict(function=name,source_module=module,charon_exit=status)
 if status==0 and not json.loads(llbc.read_text()).get('has_errors',True):
  row['llbc_sha256']=sha(llbc)
  cmd=['timeout','300',str(a),'-log','Translate','-sequential','-no-progress-bar','-abort-on-error','-strict-joins','-backend','lean','-namespace','PV_B3P_Direct17','-dest',str(gen),'-split-files','-emit-json',str(llbc)]
  status=invoke('aeneas',cmd);row['aeneas_exit']=status
  row['generated']=[dict(file=p.name,sha256=sha(p),bytes=p.stat().st_size)for p in gen.glob('*')if p.is_file()]
  emitted=(gen/'Funs.lean').read_text() if (gen/'Funs.lean').exists()else ''
  row['target_declaration_emitted']=bool(__import__('re').search(r'^def '+__import__('re').escape(module.replace('::','.')+'.'+name.replace('::','.'))+r'(?:[\s._])',emitted,__import__('re').M))
  row['status']='EXTRACTED' if status==0 and row['target_declaration_emitted'] else 'NO_EMITTED_DECLARATION' if status==0 else 'REFUSED'
 else:row['status']='CHARON REFUSED'
 results.append(row);(O/'results.json').write_text(json.dumps(results,indent=2)+'\n');print(json.dumps(row),flush=True)
print('completed',kind,len(results))
