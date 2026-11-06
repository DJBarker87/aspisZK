from pathlib import Path
import difflib,subprocess,hashlib,json
E=Path(__file__).resolve().parent
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';pins={};patch=''
for filename,mods in [('pair_forest_semantic_terminal.rs',[('NKR_schedule_native','NKR_native','NKR_schedule_native.rs.txt'),('NKR_Digest_native','NKR_digest_native','NKR_Digest_native.rs.txt')]),('pair_forest_copy_terminal.rs',[('NKR_Sum_native','NKR_sum_native','NKR_Sum_native.rs.txt')])]:
 path='crates/aspis-statement/src/pool_v1/'+filename;old=subprocess.check_output(['git','show',rev+':'+path],text=True);new=old
 for stem,mod,txt in mods:
  new+='\n#[cfg(kani)]\n#[path="'+stem+'.rs"]\nmod '+mod+';\n';code=(E/txt).read_text();name='crates/aspis-statement/src/pool_v1/'+stem+'.rs'
  patch+=''.join(difflib.unified_diff([],code.splitlines(True),fromfile='/dev/null',tofile='b/'+name));pins[name]=hashlib.sha256(code.encode()).hexdigest()
 patch+=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+path,tofile='b/'+path));pins[path]=hashlib.sha256(new.encode()).hexdigest()
path='crates/aspis-statement/src/lib.rs';old=subprocess.check_output(['git','show',rev+':'+path],text=True);new='#![cfg_attr(kani,feature(allocator_api))]\n'+old
patch+=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+path,tofile='b/'+path));pins[path]=hashlib.sha256(new.encode()).hexdigest()
(E/'NKR_native.patch').write_text(patch);(E/'NKR_SOURCE_PINS.json').write_text(json.dumps(pins))
print('Frozen scratch patch assembled and pinned')
