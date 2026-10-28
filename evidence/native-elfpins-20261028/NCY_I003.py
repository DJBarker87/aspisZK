from pathlib import Path
import json,hashlib,subprocess,re,shutil
H=Path('/home/dombarker/project-offloads/codex-cx-native-elfpins-20261028')
F=H.parent/'codex-cx-lowering2-20261026'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
r={'kind':'read-only artifact/compiler-input provenance then own rebuildable target cleanup','builds':{},'cache_seed_manifests':{}}
for label,mode in [('NCY_B001','devnet'),('NCY_B002','pool')]:
 out=H/label;target=H/('NCY_target_'+mode)
 artifacts=[{'path':str(p),'sha256':sha(p),'bytes':p.stat().st_size} for p in (out/'artifacts').glob('*.so')]
 # Preserve diagnostic JSON and hashes; the payloads contain compiler arguments, not secrets.
 diagnostics=[]
 for p in (out/'diagnostics').rglob('*'):
  if p.is_file():diagnostics.append({'path':str(p),'sha256':sha(p),'bytes':p.stat().st_size})
 seed=F/('sbf-target-pool' if mode=='pool' else 'sbf-target-verifier')
 seedpins={str(p.relative_to(seed)):sha(p) for p in seed.rglob('*') if p.is_file() and not p.is_symlink()}
 # Post-build read-only seed census, not a claim of a pre-build digest.
 cachefile=H/('NCY_'+mode+'_seed_postbuild.json');cachefile.write_text(json.dumps(seedpins,indent=2)+'\n')
 r['cache_seed_manifests'][mode]={'path':str(cachefile),'sha256':sha(cachefile),'files':len(seedpins),'timing':'post-build census; source seed never written by this lane'}
 symbol_results=[]
 for a in (out/'artifacts').glob('*.so'):
  q=subprocess.run(['/usr/bin/readelf','-Ws',str(a)],text=True,capture_output=True)
  (out/'NCY_symbols.txt').write_text(q.stdout+q.stderr)
  symbol_results.append({'command':q.args,'exit':q.returncode,'output_sha256':sha(out/'NCY_symbols.txt'),'symbol_table_lines':len(q.stdout.splitlines())})
 r['builds'][label]={'command':json.loads((out/'command.json').read_text()),'artifact':json.loads((out/'artifact.json').read_text()),'artifacts_rechecked':artifacts,'diagnostics':diagnostics,'symbols':symbol_results}
 # Only own rebuildable target dirs. Artifacts/keys, receipts, source stay retained.
 assert target.parent==H and target.name in ['NCY_target_devnet','NCY_target_pool']
 shutil.rmtree(target)
 r['builds'][label]['own_target_removed']=str(target)
cg=Path('/sys/fs/cgroup')/Path('/proc/self/cgroup').read_text().split('0::',1)[1].strip().lstrip('/')
r['limits']={n:(cg/n).read_text().strip() for n in ['memory.high','memory.max','memory.swap.max','pids.max']}
r['cgroup_memory_peak_bytes']=(cg/'memory.peak').read_text().strip();r['cgroup_swap_peak_bytes']=(cg/'memory.swap.peak').read_text().strip()
(H/'NCY_PROVENANCE.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(r),flush=True)
