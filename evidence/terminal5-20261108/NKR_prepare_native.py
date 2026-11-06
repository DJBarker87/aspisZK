from pathlib import Path
import subprocess,json,difflib,hashlib,re
E=Path(__file__).resolve().parent
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
source='crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs';lib='crates/aspis-statement/src/lib.rs'
old=subprocess.check_output(['git','show',rev+':'+source]).decode();libold=subprocess.check_output(['git','show',rev+':'+lib]).decode()
code=(E/'NKR_schedule_native.rs.txt').read_text()
def body(s,name):
 p=s.index('fn '+name+'(');p=s.index('{',p);q=p+1;depth=1
 while depth:depth+=(s[q]=='{')-(s[q]=='}');q+=1
 return s[p+1:q-1]
original=body(old,'add_schedule_lanes');trans=original.replace('semantic_initial_and_absorption(public, openings, selectors)','NKR_initial(public, openings, selectors,l)').replace('add_preweighted(packed, 0, &initial)','NKR_preweighted(packed, 0, &initial,l)').replace('add_preweighted(packed, 16, &absorption)','NKR_preweighted(packed, 16, &absorption,l)')
compact=lambda s:re.sub(r'\s+','',s)
assert compact(trans)==compact(body(code,'NKR_schedule')),'Frozen-body translation mismatch'
(E/'NKR_CONTROL_ERASURE.json').write_text(json.dumps(dict(revision=rev,source=source,original=original,translated=trans,harness=body(code,'NKR_schedule'),identity=True,source_sha256=hashlib.sha256(old.encode()).hexdigest(),harness_sha256=hashlib.sha256(code.encode()).hexdigest()),indent=2))
name='crates/aspis-statement/src/pool_v1/NKR_schedule_native.rs';new=old+'\n#[cfg(kani)]\n#[path="NKR_schedule_native.rs"]\nmod NKR_native;\n';libnew='#![cfg_attr(kani,feature(allocator_api))]\n'+libold
patch=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+source,tofile='b/'+source))
patch+=''.join(difflib.unified_diff([],code.splitlines(True),fromfile='/dev/null',tofile='b/'+name))
patch+=''.join(difflib.unified_diff(libold.splitlines(True),libnew.splitlines(True),fromfile='a/'+lib,tofile='b/'+lib))
(E/'NKR_native.patch').write_text(patch)
(E/'NKR_SOURCE_PINS.json').write_text(json.dumps({source:hashlib.sha256(new.encode()).hexdigest(),name:hashlib.sha256(code.encode()).hexdigest(),lib:hashlib.sha256(libnew.encode()).hexdigest()}))
