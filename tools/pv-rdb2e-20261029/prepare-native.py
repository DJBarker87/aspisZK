from pathlib import Path
import subprocess,re,json,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdb2e-20261029';N=E/'native';N.mkdir(exist_ok=True)
H='dombarker@100.108.41.90';D='/home/dombarker/project-offloads/codex-pv-rdb2e-20261029'
old='/home/dombarker/project-offloads/codex-pv-rdb2c-20261028'
manifest=subprocess.check_output(['ssh',H,'cat '+old+'/weights-fixture/Cargo.toml'],text=True)
manifest=re.sub(r'\[\[bin\]\].*?(?=\[profile.release\])','',manifest,count=1,flags=re.S)
manifest=re.sub(r'\n\[\[bin\]\].*','',manifest,flags=re.S)
manifest=manifest.replace('[profile.release]','sha2="=0.10.9"\ncpufeatures="=0.2.17"\nblock-buffer="=0.10.4"\n\n[profile.release]')
manifest+='\n[[bin]]\nname="associations"\npath="main.rs"\n'
(N/'Cargo.toml').write_text(manifest)
(N/'Cargo.lock').write_bytes(subprocess.check_output(['ssh',H,'cat '+old+'/weights-fixture/Cargo.lock']))
for a,b in [('sha256-soft.rs','soft.rs'),('sha256-x86.rs','x86.rs'),('sha-consts.rs','consts.rs')]: (N/b).write_bytes((E/'source'/a).read_bytes())
for name in ['sampler_original.rs','sampler_host.rs']:
 (N/name).write_bytes(subprocess.check_output(['ssh',H,'cat '+old+'/weights-fixture/'+name]))
# Record frozen Rust source directly from this worktree's git object.
paths=subprocess.check_output(['git','ls-files','*sampler.rs'],text=True).splitlines()
records=[]
for p in paths:
 if p == 'crates/aspis-r1-cost-probe/src/sampler.rs':
  raw=subprocess.check_output(['git','show','HEAD:'+p]);own=(N/'sampler_original.rs').read_bytes();assert own.startswith(raw),p
  records.append(dict(path=p,git_sha256=hashlib.sha256(raw).hexdigest(),owned_full_file_plus_audit_wrappers_sha256=hashlib.sha256(own).hexdigest(),original_byte_prefix=True))
assert records
(E/'sampler-source-binding.json').write_text(json.dumps(records,indent=2))
