from pathlib import Path
import json,subprocess,tempfile,hashlib
E=Path(__file__).resolve().parent
full=(E/'NCJ_FINAL.patch').read_text();blocks=full.split('--- ');kmx='';parts=[]
for b in blocks[1:]:
 b='--- '+b
 if '\n+++ b/KMX_stubs.rs\n' in b:kmx=b
 else:parts.append(b)
assert kmx
mitigation=subprocess.check_output(['git','show','HEAD:evidence/kani-mitig-20261028/KMX_copy_stubs.patch'])
assert hashlib.sha256(mitigation).hexdigest()=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
patch=''.join(parts);(E/'NCJ_FINAL_HARNESS.patch').write_text(patch)
receipt=json.loads((E/'NCJ_K070/receipt.json').read_text());checked={};extra={}
with tempfile.TemporaryDirectory(prefix='NCJ_patch_replay_') as tmp:
 root=Path(tmp)
 for b in parts:
  line=b.splitlines()[0]
  if not line.startswith('--- a/'):continue
  name=line[6:];data=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+name]);p=root/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
 for data in [mitigation,patch.encode()]:
  r=subprocess.run(['git','apply','--whitespace=nowarn','-'],input=data,cwd=root,capture_output=True);assert r.returncode==0,r.stderr
 for p in root.rglob('*'):
  if not p.is_file():continue
  name=str(p.relative_to(root));sha=hashlib.sha256(p.read_bytes()).hexdigest()
  if name in ['KMX_native.rs','KMX_CopyMeaning.lean']:extra[name]=sha;continue
  assert sha==receipt['source_hashes']['NCJ_src/'+name],name;checked[name]=sha
(E/'NCJ_PATCH_REPLAY.json').write_text(json.dumps(dict(frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',mitigation_sha256=hashlib.sha256(mitigation).hexdigest(),harness_patch_sha256=hashlib.sha256(patch.encode()).hexdigest(),files_match_final_K070_receipt=checked,additional_exact_mitigation_files=extra,compile_rerun=False),indent=2)+'\n')
print('Exact mitigation + harness overlay reproduces all8 patched files in final native receipt')
