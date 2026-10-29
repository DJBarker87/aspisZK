"""Direct deployed-source extraction; restored ae1-2 translator, no ports."""
from run import H,run
from pathlib import Path
import hashlib,json,subprocess,sys
stage,group,ident=sys.argv[1:];assert stage in ('charon','aeneas');assert group in ('terminal','copy','field','poseidon','statement-copy');assert 73900<=int(ident)<=73929
R=H/'resume17';R.mkdir(exist_ok=True);root=R/group;root.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
c=Path('/home/dombarker/project-offloads/codex-pv-extract-20261027/charon');a=Path('/home/dombarker/project-offloads/codex-pv-cx-20261029/resume-ae1/pinned-tools/aeneas-ae1-2-fda587d2')
assert sha(c)=='daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8'
assert sha(a)=='fda587d25a66604a973bbc2947a4416ba373b56dd8c98655991c1b6eaa240b68'
assert len(list(R.glob('N*/receipt/receipt.json')))<30
label='N'+ident; retry=0
while (R/label).exists():
 assert not (R/label/'receipt/receipt.json').exists(),'charged native ID cannot be reused'
 retry+=1;label='N'+ident+'-r'+str(retry)
driver={'terminal':'terminal','copy':'terminal','field':'field','poseidon':'poseidon','statement-copy':'poseidon'}[group]
manifest=H/('source/tools/pv-b3p6-20261028/v244-direct17-'+driver+'/Cargo.toml')
features={'terminal':'ct-host-prover','copy':'ct-host-prover','field':'r0,ct-host-prover','poseidon':'r0,pool-v1-kernel,aspis-core/ct-host-prover','statement-copy':'r0,pool-v1-kernel,aspis-core/ct-host-prover'}[group]
import shutil
if not manifest.with_name('Cargo.lock').exists():shutil.copy2(manifest.parent.parent/'v244/Cargo.lock',manifest.with_name('Cargo.lock'))
config=json.loads((H/'features227-resume4.json').read_text());assert config['feature_differences']==[]
meta=json.loads(subprocess.check_output(['cargo','+1.94.1','metadata','--offline','--format-version','1','--manifest-path',str(manifest),'--features',features],text=True))
pkgs={p['id']:p for p in meta['packages']};nodes=[dict(name=pkgs[n['id']]['name'],version=pkgs[n['id']]['version'],source=pkgs[n['id']]['source'],features=n['features']) for n in meta['resolve']['nodes']]
expected={n['name']:n['features'] for n in config['validation']['nodes'] if n['name'] in ('aspis-core','aspis-statement','aspis-r1-cost-probe')}
for n in nodes:
 if n['name'] in expected and n['name']!='aspis-r1-cost-probe':assert n['features']==expected[n['name']],(n,expected[n['name']])
sources=json.loads((R/'deployed-source-pins.json').read_text())
for p,h in sources.items():assert sha(H/'source'/p)==h,(p,h)
mods={'terminal':'aspis_r1_cost_probe::host_terminal','copy':'aspis_r1_cost_probe::host_copy_terminal','field':'aspis_core::field','poseidon':'aspis_statement::state_only_poseidon','statement-copy':'aspis_statement::pool_v1::pair_forest_copy_terminal'}
llbc=root/'Deployed17.llbc'
if stage=='charon':
 cmd=['timeout','300','taskset','--cpu-list','0-3',str(c),'cargo','--preset','aeneas','--mir','optimized','--sysroot','default','--start-from','crate::'+mods[group].split('::',1)[1],'--include','crate::'+mods[group].split('::',1)[1],'--include','aspis_core::field','--include','aspis_r1_cost_probe::host_terminal_field','--dest-file',str(llbc),'--','--manifest-path',str(manifest),'--release','--locked','--offline','--lib','--jobs','4','--features',features]
 # Starting only from the 36 required functions excludes unrelated derived/default methods.
 roots=json.loads((R/'direct-roots.json').read_text())[group]
 j=cmd.index('--start-from');cmd[j:j+2]=sum((['--start-from','crate::'+mods[group].split('::',1)[1]+'::'+n] for n in roots),[])
else:
 data=json.loads(llbc.read_text());assert not data.get('has_errors',False),'do not translate erroneous LLBC'
 (root/'generated').mkdir(exist_ok=True)
 cmd=['timeout','300',str(a),'-sequential','-no-progress-bar','-abort-on-error','-strict-joins','-backend','lean','-namespace','PV_B3P_Direct17'+group.title().replace('-',''),'-dest',str(root/'generated'),'-split-files','-emit-json',str(llbc)]
inputs=dict(stage=stage,group=group,command=cmd,charon_sha256=sha(c),aeneas_sha256=sha(a),translator_identity='functionally identical rebuild (ae1-2)',translator_authority='codex/pv-cx-20261029:evidence/pv-cx2-20261029/translator-identity.json',source_revision=(R/'revision').read_text().strip(),source_pins=sources,features=nodes,profile=dict(opt_level=3,debug_assertions=False,overflow_checks=False),extractor_toolchain='nightly-2026-06-01',deployed_toolchain='1.94.1',std_transfer='x-prime comparison required before credit',input_llbc_sha256=sha(llbc) if stage=='aeneas' else None)
(R/('N'+ident+'-inputs.json')).write_text(json.dumps(inputs,indent=2)+'\n')
r=run('resume17/'+label,cmd,'direct deployed '+group+' '+stage+'; time in optimized compilation/translation, no arithmetic proof generation',{'RUSTUP_TOOLCHAIN':'nightly-2026-06-01','CARGO_TARGET_DIR':str(H/'charon-target'),'PV_REV':inputs['source_revision'],'CARGO_PROFILE_RELEASE_OPT_LEVEL':'3','CARGO_PROFILE_RELEASE_DEBUG_ASSERTIONS':'false','CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS':'false'})
print('status',r)
if (R/label/'receipt').exists():
 for n in ('stdout.log','stderr.log'):print((R/label/'receipt'/n).read_text()[-5000:])
raise SystemExit(r)
