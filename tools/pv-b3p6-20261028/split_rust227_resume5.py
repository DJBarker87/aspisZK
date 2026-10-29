"""Split two overlong owned reference bodies; frozen shipped files untouched.
Per-input/per-lane arithmetic expression and accumulator order are retained.
All pure-copy/frame and grouping obligations remain explicit, not auto-credited.
"""
from pathlib import Path
import subprocess,re,json,hashlib
P=Path('tools/pv-b3p6-20261028/v244');D=Path('evidence/pv-b3p6-20261028');base='540ba075d514657e83770731c71dd66cdfbb56c3'
get=lambda n:subprocess.check_output(['git','show',base+':'+str(P/n)],text=True)
tok=lambda s:re.findall(r'\w+|[^\s]',s)
f=get('reference_field.rs');a=f.index('pub(crate) fn qm31_sum_products3_prepared');b=f.index('pub(crate) fn qm31_m31_dot',a);old=f[a:b];blocks=re.findall(r'\{ let index=([012])usize;\n(.*?)    \}\n',old,re.S);assert [k for k,_ in blocks]==['0','1','2']
parts=[v.replace('left[index]','left').replace('right[index]','right')for _,v in blocks];assert all(tok(v)==tok(parts[0])for v in parts)
helper='fn accumulate_prepared227(mut sums:[[u64;3];3],right:QM31,left:PreparedQm31Multiplier)->[[u64;3];3] {\n'+parts[0]+'    sums\n}\n'
suffix=old[old.index('    let m0=reconstruct_component'):]
new=helper+'pub(crate) fn qm31_sum_products3_prepared(left:&[PreparedQm31Multiplier;3],right:&[QM31;3])->QM31 {\n    let mut sums=[[0u64;3];3];\n'+''.join(f'    sums=accumulate_prepared227(sums,right[{i}],left[{i}]);\n'for i in range(3))+suffix
f=f[:a]+new+f[b:];(P/'reference_field.rs').write_text(f)
s=get('reference_poseidon.rs');a=s.index('fn internal_linear_lazy(');b=s.index('\n#[inline(never)]\nfn full_round(',a);old_poseidon=s[a:b]
shifts=[0,1,2,3,4,5,6,7,8,10,12,13,14,15,16];assert all(f'SHIFTS[{i}usize - 1]'in old_poseidon for i in range(1,16))
# Confirm the reached 15x4 accumulation order before replacing its boundaries.
accum=re.findall(r'part_sum\[(\d)usize\] \+= u64::from\(limbs\[\1usize\]\);',old_poseidon);assert list(map(int,accum))==list(range(4))*15
new='fn internal_linear_lazy(state:&mut[QM31;16]) {\n    const SHIFTS:[u8;15]=['+','.join(map(str,shifts))+'];\n    let old_zero=extension_limbs(state[0]);\n    let mut part_sum=[0u64;4];\n'
for i in range(1,16):new+=f'    part_sum=internal_sum227(part_sum,state[{i}]);\n'
new+='    let full_sum=internal_full_sum227(part_sum,old_zero);\n    state[0]=internal_zero227(part_sum,old_zero);\n'
for i in range(1,16):new+=f'    state[{i}]=internal_shift227(state[{i}],full_sum,SHIFTS[{i-1}]);\n'
new+='}\n'
helpers='\nfn internal_sum227(mut part_sum:[u64;4],value:QM31)->[u64;4] {\n    let limbs=extension_limbs(value);\n'+''.join(f'    part_sum[{j}]+=u64::from(limbs[{j}]);\n'for j in range(4))+'    part_sum\n}\n'
helpers+='fn internal_full_sum227(part_sum:[u64;4],old_zero:[u32;4])->[u64;4] {\n    ['+','.join(f'part_sum[{j}]+u64::from(old_zero[{j}])'for j in range(4))+']\n}\n'
helpers+='fn internal_zero227(part_sum:[u64;4],old_zero:[u32;4])->QM31 {\n    extension_from_raw_limbs(['+','.join(f'part_sum[{j}]+u64::from(P)-u64::from(old_zero[{j}])'for j in range(4))+'])\n}\n'
helpers+='fn internal_shift227(value:QM31,full_sum:[u64;4],shift:u8)->QM31 {\n    let limbs=extension_limbs(value);\n    extension_from_raw_limbs(['+','.join(f'full_sum[{j}]+(u64::from(limbs[{j}])<<shift)'for j in range(4))+'])\n}\n'
s=s[:a]+new+s[b:]+helpers;(P/'reference_poseidon.rs').write_text(s)
record=dict(base=base,field_sha256=hashlib.sha256(f.encode()).hexdigest(),poseidon_sha256=hashlib.sha256(s.encode()).hexdigest(),prepared_pair_bodies_token_identical=True,accumulations=list(map(int,accum)),shifts=shifts,differences=['prepared3: three helper calls thread the same 3x3 accumulator; bounded immutable pair copies occur before helper arithmetic','internal linear: fifteen same-order four-limb sum helpers, then identical full/zero sums, then same-order lane shifts/writes','helper argument copies are pure and bounded; complete Result, copy/index/frame/grouping law application still required'],source_link_credit=False,previous_attempts=[42050,42051,42053,42054,42056],no_cap_increase=True)
(D/'split-rust227-resume5.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record))
