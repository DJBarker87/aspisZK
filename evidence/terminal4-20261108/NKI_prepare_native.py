from pathlib import Path
import subprocess,json,difflib,hashlib,re
E=Path(__file__).resolve().parent
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
source='crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs';lib='crates/aspis-statement/src/lib.rs'
old=subprocess.check_output(['git','show',rev+':'+source]).decode();libold=subprocess.check_output(['git','show',rev+':'+lib]).decode()
code=(E/'NKI_append_native.rs.txt').read_text()
def body(s,name):
 p=s.index('fn '+name+'(');p=s.index('{',p);q=p+1;depth=1
 while depth:depth+=(s[q]=='{')-(s[q]=='}');q+=1
 return s[p+1:q-1]
original=body(old,'append_level_packed_selector_tensor');trans=original
# Each residual occurrence is replaced textually; grouping/order preserved exactly.
for base,expected in [('RATE','expected'),('','frontier')]:
 for k in range(8):
  ix=(base if k==0 else base+' + '+str(k)) if base else str(k)
  target=expected+'['+str(k)+']'
  if base and k==7:target+=' .add(MERKLE_NODE_COMPRESSION_V3_TWEAK)'
  oldexpr='opened['+ix+'].sub(lift_m31('+target+'))'
  if base and k==7:
   oldexpr='opened[RATE + 7]\n                .sub(lift_m31(expected[7].add(MERKLE_NODE_COMPRESSION_V3_TWEAK)))'
   target='NKI_tweak(expected[7],MERKLE_NODE_COMPRESSION_V3_TWEAK,l)'
  assert oldexpr in trans,oldexpr
  trans=trans.replace(oldexpr,'NKI_sub(opened['+ix+'],NKI_lift('+target+',l),l)')
trans=trans.replace('PreparedQm31Multiplier::new(high)','NKI_new(high,l)').replace('empty_root(level)','NKI_empty(level,l)')
for k in range(2):trans=trans.replace('prepared_high.mul(qm31_pack_base4(&residual'+str(k)+'))','NKI_mul(prepared_high,NKI_pack(&residual'+str(k)+',l),l)')
compact=lambda s:re.sub(r'\s+','',s)
assert compact(trans)==compact(body(code,'NKI_append')),'Frozen-body translation mismatch'
(E/'NKI_CONTROL_ERASURE.json').write_text(json.dumps(dict(revision=rev,source=source,original=original,translated=trans,harness=body(code,'NKI_append'),identity=True,source_sha256=hashlib.sha256(old.encode()).hexdigest()),indent=2))
name='crates/aspis-statement/src/pool_v1/NKI_append_native.rs';new=old+'\n#[cfg(kani)]\n#[path="NKI_append_native.rs"]\nmod NKI_native;\n';libnew='#![cfg_attr(kani,feature(allocator_api))]\n'+libold
patch=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+source,tofile='b/'+source))
patch+=''.join(difflib.unified_diff([],code.splitlines(True),fromfile='/dev/null',tofile='b/'+name))
patch+=''.join(difflib.unified_diff(libold.splitlines(True),libnew.splitlines(True),fromfile='a/'+lib,tofile='b/'+lib))
(E/'NKI_native.patch').write_text(patch)
(E/'NKI_SOURCE_PINS.json').write_text(json.dumps({source:hashlib.sha256(new.encode()).hexdigest(),name:hashlib.sha256(code.encode()).hexdigest(),lib:hashlib.sha256(libnew.encode()).hexdigest()}))
