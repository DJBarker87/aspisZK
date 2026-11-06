from pathlib import Path
import subprocess,re,json,hashlib,difflib
E=Path(__file__).resolve().parent
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
source='crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs'
lib='crates/aspis-statement/src/lib.rs'
old=subprocess.check_output(['git','show',rev+':'+source],text=True)
libold=subprocess.check_output(['git','show',rev+':'+lib],text=True)
code=(E/'NKR_Digest_native.rs.txt').read_text()
def body(s,name):
 p=s.index('fn '+name+'(');p=s.index('{',p);q=p+1;depth=1
 while depth:depth+=(s[q]=='{')-(s[q]=='}');q+=1
 return s[p+1:q-1]
full=body(old,'public_digest_packed_selector_tensor')
prefix=full[:full.index('    let source = public.transition.live_snapshot;')]
trans=prefix
for orig,new in [('left_digest_packed_selector_tensor','NKR_Digest_left'),('optional_recipient_packed_selector_tensor','NKR_Digest_recipient')]:
 while orig+'(' in trans:
  start=trans.index(orig+'(');p=start+len(orig);q=p+1;depth=1
  while depth:depth+=(trans[q]=='(')-(trans[q]==')');q+=1
  args=trans[p+1:q-1].rstrip().rstrip(',')
  trans=trans[:start]+new+'('+args+',l)'+trans[q:]
trans=re.sub(r'local_sums\[1\]\[([01])\] = local_sums\[1\]\[\1\]\.add\((\w+)\[\1\]\);',r'local_sums[1][\1] = NKR_Digest_add(local_sums[1][\1],\2[\1],l);',trans)
trans+='    local_sums\n'
compact=lambda s:re.sub(r'\s+','',s)
assert compact(trans)==compact(body(code,'NKR_Digest_prefix')),'Frozen prefix translation mismatch'
pins=dict(revision=rev,function='public_digest_packed_selector_tensor',source=source,source_sha256=hashlib.sha256(old.encode()).hexdigest(),full_body_sha256=hashlib.sha256(full.encode()).hexdigest(),prefix_sha256=hashlib.sha256(prefix.encode()).hexdigest(),harness_sha256=hashlib.sha256(code.encode()).hexdigest(),prefix=prefix,translated=trans,identity=True,scope='first four calls and eight additions only')
(E/'NKR_Digest_ERASURE.json').write_text(json.dumps(pins,indent=1))
new=old+'\n#[cfg(kani)]\n#[path="NKR_Digest_native.rs"]\nmod NKR_Digest_native;\n'
libnew='#![cfg_attr(kani,feature(allocator_api))]\n'+libold
name='crates/aspis-statement/src/pool_v1/NKR_Digest_native.rs'
patch=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+source,tofile='b/'+source))
patch+=''.join(difflib.unified_diff([],code.splitlines(True),fromfile='/dev/null',tofile='b/'+name))
patch+=''.join(difflib.unified_diff(libold.splitlines(True),libnew.splitlines(True),fromfile='a/'+lib,tofile='b/'+lib))
(E/'NKR_Digest_native.patch').write_text(patch)
(E/'NKR_Digest_SOURCE_PINS.json').write_text(json.dumps({source:hashlib.sha256(new.encode()).hexdigest(),name:hashlib.sha256(code.encode()).hexdigest(),lib:hashlib.sha256(libnew.encode()).hexdigest()}))
print('NKR digest prefix frozen-control erasure identity PASS')
