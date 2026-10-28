"""Own scratch source selection: symlink frozen files read-only, private cfg harness.
No shared workspace or infrastructure writes. No corpus duplication.
"""
from pathlib import Path
import subprocess,json,shlex,base64
E=Path(__file__).resolve().parent
H='dombarker@100.108.41.90'
B='/home/dombarker/project-offloads/codex-cx-native-prepare1-20261027'
S='/home/dombarker/project-offloads/codex-cx-leaf-p6-13-20261027/LPo_src'
# Enumerate the existing corpus only; all native modifications below use frozen
# git contents privately. A source pin audit rejects any unexpected mismatch.
code=f'''from pathlib import Path
import hashlib,json
s=Path({S!r})
print(json.dumps({{str(p.relative_to(s)):hashlib.sha1(b'blob '+str(p.stat().st_size).encode()+b'\\0'+p.read_bytes()).hexdigest() for p in s.rglob('*') if p.is_file()}}))
'''
r=subprocess.run(['ssh',H,'python3'],input=code,capture_output=True,text=True);assert r.returncode==0,r.stderr
available=json.loads(r.stdout)
records=subprocess.check_output(['git','ls-tree','-r','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'],text=True)
files={};replacements={}
for line in records.splitlines():
 info,name=line.split('\t');mode,kind,sha=info.split()
 if name not in available:continue
 files[name]=sha
 if available[name]!=sha or name in ['Cargo.lock','crates/aspis-r1-cost-probe/src/verifier.rs','crates/aspis-r1-cost-probe/src/candidate.rs','crates/aspis-core/src/r0_transcript.rs','crates/aspis-r1-cost-probe/src/sampler.rs']:
  replacements[name]=base64.b64encode(subprocess.check_output(['git','cat-file','blob',sha])).decode()
for name in ['Cargo.toml','Cargo.lock','.cargo/config.toml','crates/aspis-r1-cost-probe/src/verifier.rs']:
 assert name in files,name
payload={'files':files,'private':replacements,'harness':__import__('NBA_harness').source(),'core':__import__('NBA_harness').source('crates/aspis-core/src/NBA_query_core.rs'),'sampler':__import__('NBA_harness').source('crates/aspis-r1-cost-probe/src/NBA_sampler.rs')}
code=f'''from pathlib import Path
import json,base64,hashlib,difflib
b=Path({B!r});s=Path({S!r});dst=b/'NBA_src';x=json.loads({json.dumps(json.dumps(payload))})
dst.mkdir(exist_ok=True)
for rel,sha in x['files'].items():
 p=dst/rel;p.parent.mkdir(parents=True,exist_ok=True)
 if rel in x['private']:
  if p.is_symlink():p.unlink()
  p.write_bytes(base64.b64decode(x['private'][rel]))
 elif not p.exists():p.symlink_to(s/rel)
 data=p.read_bytes();assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\\0'+data).hexdigest()==sha,rel
p=dst/'crates/aspis-r1-cost-probe/src/verifier.rs'
original=p.read_text();p.write_text(original+'\\n#[cfg(kani)] mod NBA_verifier {{ include!("NBA_verifier.rs"); }}\\n')
h=dst/'crates/aspis-r1-cost-probe/src/NBA_verifier.rs';h.write_text(x['harness'])
patch=''.join(difflib.unified_diff(original.splitlines(True),p.read_text().splitlines(True),fromfile='a/crates/aspis-r1-cost-probe/src/verifier.rs',tofile='b/crates/aspis-r1-cost-probe/src/verifier.rs'))
patch+=''.join(difflib.unified_diff([],h.read_text().splitlines(True),fromfile='/dev/null',tofile='b/crates/aspis-r1-cost-probe/src/NBA_verifier.rs'))
p=dst/'crates/aspis-core/src/r0_transcript.rs';old=p.read_text();p.write_text(old+'\\n#[cfg(kani)] mod NBA_query {{ include!("NBA_query_core.rs"); }}\\n')
h=dst/'crates/aspis-core/src/NBA_query_core.rs';h.write_text(x['core'])
patch+=''.join(difflib.unified_diff(old.splitlines(True),p.read_text().splitlines(True),fromfile='a/crates/aspis-core/src/r0_transcript.rs',tofile='b/crates/aspis-core/src/r0_transcript.rs'))
patch+=''.join(difflib.unified_diff([],h.read_text().splitlines(True),fromfile='/dev/null',tofile='b/crates/aspis-core/src/NBA_query_core.rs'))
p=dst/'crates/aspis-r1-cost-probe/src/sampler.rs';old=p.read_text();p.write_text(old+'\\n#[cfg(kani)] mod NBA_sampler {{ include!("NBA_sampler.rs"); }}\\n')
h=dst/'crates/aspis-r1-cost-probe/src/NBA_sampler.rs';h.write_text(x['sampler'])
patch+=''.join(difflib.unified_diff(old.splitlines(True),p.read_text().splitlines(True),fromfile='a/crates/aspis-r1-cost-probe/src/sampler.rs',tofile='b/crates/aspis-r1-cost-probe/src/sampler.rs'))
patch+=''.join(difflib.unified_diff([],h.read_text().splitlines(True),fromfile='/dev/null',tofile='b/crates/aspis-r1-cost-probe/src/NBA_sampler.rs'))
(b/'NBA_harness.patch').write_text(patch)
print(json.dumps(dict(files=len(x['files']),private=len(x['private']),patch=patch,source_sha256={{rel:hashlib.sha256((dst/rel).read_bytes()).hexdigest() for rel in x['files']}})))
'''
r=subprocess.run(['ssh',H,'python3'],input=code,capture_output=True,text=True);assert r.returncode==0,r.stderr
out=json.loads(r.stdout);(E/'NBA_harness.patch').write_text(out.pop('patch'))
(E/'NBA_SOURCE.json').write_text(json.dumps(out,indent=2)+'\n')
