"""V244 deployed-profile preflight and finite differential. No Kani/extractor fallback."""
from pathlib import Path
import subprocess,json,hashlib,sys
from run import H,run
root=H/'source';p=root/'tools/pv-b3p6-20261028/v244'
features=['r1p-check','aspis-r1-cost-probe/ct-host-prover']
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def command(cmd):
 r=subprocess.run(cmd,cwd=root,text=True,capture_output=True)
 assert r.returncode==0,(cmd,r.returncode,r.stderr)
 return r.stdout

def metadata(manifest,feat=(),locked=False):
 cmd=['cargo','+1.94.1','metadata','--offline','--format-version','1','--manifest-path',str(manifest)]
 if locked:cmd+=['--locked']
 if feat:cmd+=['--features',','.join(feat)]
 raw=command(cmd);d=json.loads(raw);pkgs={x['id']:x for x in d['packages']}
 return dict(command=cmd,raw_sha256=hashlib.sha256(raw.encode()).hexdigest(),nodes=[dict(name=pkgs[x['id']]['name'],version=pkgs[x['id']]['version'],source=pkgs[x['id']]['source'],features=x['features'])for x in d['resolve']['nodes']])
kind=sys.argv[1]
if kind=='preflight':
 freeze=json.loads((H/'source-freeze-resume4.json').read_text());bad=[n for n,s in freeze.items() if not (root/n).is_file() or sha(root/n)!=s];assert not bad,bad
 (p/'Cargo.lock').write_bytes((root/'tools/r1-cost-probe/Cargo.lock').read_bytes())
 a=metadata(root/'tools/r1-cost-probe/Cargo.toml',features,True);b=metadata(p/'Cargo.toml')
 diff=[]
 for n in b['nodes']:
  if n['name']=='pv-b3p6-reference227':continue
  candidates=[x for x in a['nodes'] if all(x[k]==n[k]for k in ['name','version','source'])]
  assert len(candidates)==1,('deployed dependency mismatch',n,candidates)
  if n['features']!=candidates[0]['features']:diff.append(dict(crate=n['name'],version=n['version'],source=n['source'],deployed=candidates[0]['features'],validation=n['features']))
 reached=['aspis-core','aspis-statement','aspis-prover','aspis-r1-cost-probe']
 assert not [x for x in diff if x['crate']in reached],diff
 sysroot=Path(command(['rustup','run','1.94.1','rustc','--print','sysroot']).strip())
 std=sysroot/'lib/rustlib/src/rust/library';assert std.is_dir()
 stdrows={str(f.relative_to(std)):sha(f)for f in sorted(std.rglob('*.rs'))}
 charon=Path('/home/dombarker/project-offloads/codex-pv-extract-20261027/charon')
 pinned=command([str(charon),'toolchain-version']).strip()
 assert sha(charon)=='daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8'
 info=dict(revision=(H/'revision').read_text().strip(),deployed=a,validation=b,feature_differences=diff,reached_crates=reached,
 profile=dict(name='release',opt_level=3,overflow_checks=False,debug_assertions=False,cfg_test=False),
 rustc=command(['rustup','run','1.94.1','rustc','-vV']).strip(),std_source_path=str(std),std_sources=stdrows,std_source_tree_sha256=hashlib.sha256(json.dumps(stdrows,sort_keys=True).encode()).hexdigest(),
 deployed_lock_sha256=sha(root/'tools/r1-cost-probe/Cargo.lock'),validation_lock_sha256=sha(p/'Cargo.lock'),
 pinned_charon=dict(path=str(charon),sha256=sha(charon),required_toolchain=pinned,required_compiler=command(['rustup','run',pinned,'rustc','-vV']).strip(),toolchain_path=command([str(charon),'toolchain-path']).strip()),
 source_freeze_checked=len(freeze),no_kani=True)
 (H/'features227-resume4.json').write_text(json.dumps(info,indent=2)+'\n')
 print(json.dumps(dict(features_equal_on_reached_crates=True,other_feature_differences=diff,rustc=info['rustc'].splitlines()[0],std_files=len(stdrows),charon_toolchain=pinned)))
 assert not diff,('feature parity must be complete before gate launch',diff)
 sys.exit(0)
assert kind=='native'
x=json.loads((H/'features227-resume4.json').read_text());assert x['profile']['cfg_test']is False
label='native227-resume4-errors';i=0
while (H/label).exists():
 assert not (H/label/'receipt/receipt.json').exists(),'charged gate cannot be rerun unchanged'
 i+=1;label='native227-resume4-errors-r'+str(i)
cmd=['timeout','300','taskset','--cpu-list','0-3','cargo','+1.94.1','run','--release','--locked','--offline','--manifest-path',str(p/'Cargo.toml'),'--bin','finite227','--jobs','4']
sys.exit(run(label,cmd,'time expected in optimized Rust compilation, then one named finite differential across host/owned/statement terminal Results; no dense arithmetic release gate or proof generation; cfg(test) disabled',{'RUSTFLAGS':'-C link-arg=-Wl,--threads=4'}))
