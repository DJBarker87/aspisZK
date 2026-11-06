from pathlib import Path
import json,hashlib,difflib,subprocess,re
E=Path(__file__).resolve().parent;P=E.parent/'terminal2-20261108';rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
source='crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs'
original=subprocess.check_output(['git','show',rev+':'+source]).decode();lib='crates/aspis-statement/src/lib.rs';libold=subprocess.check_output(['git','show',rev+':'+lib]).decode()
code=(E/'NJX_digest_native.rs.txt').read_text()
def body(s,name):
 p=s.index('fn '+name+'(');p=s.index('{',p);depth=1;q=p+1
 while depth:
  depth+=(s[q]=='{')-(s[q]=='}');q+=1
 return s[p+1:q-1]
left=body(original,'left_digest_packed_selector_tensor');translated=left.replace('PreparedQm31Multiplier::new(high)','NJX_new(high,l)')
translated=re.sub(r'opened\[(\d)\]\.sub\(lift_m31\(expected\[\1\]\)\)',lambda m:f'NJX_sub(opened[{m[1]}],NJX_lift(expected[{m[1]}],l),l)',translated)
translated=re.sub(r'prepared_high\.mul\(qm31_pack_base4\(&residual(\d)\)\)',lambda m:f'NJX_mul(prepared_high,NJX_pack(&residual{m[1]},l),l)',translated)
compact=lambda s:re.sub(r'\s+','',s).replace(',]',']')
assert compact(translated)==compact(body(code,'NJX_left')),'Frozen left body erasure mismatch'
carry=body(original,'optional_carry_packed_selector_tensor');c=carry.index('if carry < 20 {');inside=carry[c+len('if carry < 20 {'):carry.index('} else {')]
assert compact(inside.replace('frontier','expected'))==compact(left),'carry true body differs from frozen left'
assert compact(carry[carry.index('} else {')+len('} else {'):].rsplit('}',1)[0])=='[QM31::ZERO;DIGEST_ELEMS/4]'
(E/'NJX_CONTROL_ERASURE.json').write_text(json.dumps(dict(revision=rev,source=source,source_sha256=hashlib.sha256(original.encode()).hexdigest(),left_original_body=left,left_translated_body=translated,left_harness_body=body(code,'NJX_left'),carry_original_body=carry,checks=['frozen left body byte-token identity after only named child replacement','carry true arm identical to left body; else zero','all8subtractions before both pack/product calls'],new_trust=False),indent=2))
name='crates/aspis-statement/src/pool_v1/NJX_digest_native.rs';suffix='\n#[cfg(kani)]\n#[path="NJX_digest_native.rs"]\nmod NJX_native;\n';new=original+suffix;libnew='#![cfg_attr(kani,feature(allocator_api))]\n'+libold
patch=''.join(difflib.unified_diff(original.splitlines(True),new.splitlines(True),fromfile='a/'+source,tofile='b/'+source))
patch+=''.join(difflib.unified_diff([],code.splitlines(True),fromfile='/dev/null',tofile='b/'+name))
patch+=''.join(difflib.unified_diff(libold.splitlines(True),libnew.splitlines(True),fromfile='a/'+lib,tofile='b/'+lib))
(E/'NJX_native.patch').write_text(patch)
(E/'NJX_SOURCE_PINS.json').write_text(json.dumps({source:hashlib.sha256(new.encode()).hexdigest(),name:hashlib.sha256(code.encode()).hexdigest(),lib:hashlib.sha256(libnew.encode()).hexdigest()}))
x=json.loads((E/'NJX_L012.json').read_text());x.pop('deps_fingerprint',None);x.update(attempt='NJX_L031',kind='setup',module='NJX_stage_native',sources=['NJX_stage_native.py','NJX_FROZEN_INPUTS.json.xz','NJX_FROZEN_INPUTS.json.sha256','NJX_EXTRA_INPUTS.json','NJX_KMX.patch','NJX_native.patch','NJX_SOURCE_PINS.json','NJX_FROZEN_FILE_PINS.json','NJX_CONTROL_ERASURE.json','NJX_digest_native.rs.txt','NJX_prepare_native.py'],command=['python3','NJX_stage_native.py'],expected_time='Small frozen-source staging only; no prover or extraction',collect=[]);(E/'NJX_L031.json').write_text(json.dumps(x))
B='/home/dombarker/project-offloads/codex-cx-terminal3-20261108'
for k,(name,invert) in enumerate([('NJX_left_global_cut',False),('NJX_left_global_cut',True),('NJX_carry_global_cut',False),('NJX_carry_global_cut',True)],1):
 x=json.loads((P/'NJL_K057.json').read_text());a=f'NJX_K{k:03}';x.pop('deps_fingerprint',None);x.update(attempt=a,module=name,command=['python3','NJX_gate.py',a+'.json'],sources=['NJX_gate.py','NJX_SOURCE_PINS.json','NJX_FROZEN_FILE_PINS.json','NJX_EXTRA_INPUTS.json','NJX_CONTROL_ERASURE.json','NJX_digest_native.rs.txt','NJX_native.patch','NJX_KMX.patch','NJX_PREDECESSOR_EXPORT.json','NJX_NJO_EXPORT.json'],expected_time='Optimized compilation then named global source-order/copy frame elimination; field arithmetic is opaque and Lean-discharged')
 x['native_command']=[v.replace('codex-cx-terminal2-20261108','codex-cx-terminal3-20261108').replace('NJL_src','NJX_src').replace('NJL_target','NJX_target').replace('pool_v1::pair_forest_copy_terminal::NJL_native::NJL_append_group_cut','pool_v1::pair_forest_semantic_terminal::NJX_native::'+name)for v in x['native_command']]
 x['env']['CARGO_TARGET_DIR']=B+'/NJX_target';x['env']['TMPDIR']=B+'/NJX_tmp';x['env']['RUSTFLAGS']='-Copt-level=3 -C link-arg=-Wl,--threads=1'+(' --cfg NJX_invert' if invert else '');x['collect']=[v.replace('NJL_K057',a) for v in x['collect']];(E/(a+'.json')).write_text(json.dumps(x))
print('Two frozen-body cuts, matched controls and exact erasure checks prepared')
