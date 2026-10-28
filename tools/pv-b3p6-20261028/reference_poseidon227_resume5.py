"""Owned projected Poseidon reference: fixed-order closure/iterator elimination."""
from pathlib import Path
import re,hashlib,json
P=Path('tools/pv-b3p6-20261028/v244');source=Path('crates/aspis-statement/src/state_only_poseidon.rs').read_text();constants=Path('crates/aspis-statement/src/poseidon2.rs').read_text()
head='''use aspis_core::field::{qm31_m31_dot,qm31_pack_base4,qm31_sum_products3_prepared,qm31_sum_products4,PreparedQm31Multiplier,CM31,M31,P,QM31};
use aspis_statement::poseidon2::{POSEIDON2_WIDTH,RATE};
use aspis_statement::state_only_poseidon::{StateOnlyPoseidonOpenings,StateOnlyPoseidonSelectors,STATE_ONLY_POSEIDON_PACKED_LANES};
macro_rules! array4 { ($index:ident,$body:expr) => {{
    let mut output=[{let $index=0usize;$body},{let $index=1usize;$body},{let $index=2usize;$body},{let $index=3usize;$body}];
    output
}}; }
'''
cs=[]
for name in ['EXTERNAL_INITIAL','EXTERNAL_FINAL','INTERNAL']:
 m=re.search(r'pub\(crate\) const '+name+r':.*?\n\];',constants,re.S);assert m,name;cs.append(m[0])
s=head+'\n'.join(cs)+'\n'+source[source.index('fn lift('):source.index('fn multilinear_evaluate(')]
s=re.sub(r'core::array::from_fn\(\|(\w+)\|',r'array4!(\1,',s)
s=s.replace('input.map(extension_limbs)','[extension_limbs(input[0]),extension_limbs(input[1]),extension_limbs(input[2]),extension_limbs(input[3])]')
s=s.replace('local_packed.map(|value| value.add(sum))','[local_packed[0].add(sum),local_packed[1].add(sum),local_packed[2].add(sum),local_packed[3].add(sum)]')
for lhs,body in [('weights','local[row]'),('even_constants','M31(INTERNAL[2 * (row - 2)])'),('odd_constants','M31(INTERNAL[2 * (row - 2) + 1])')]:
 old=f'let {lhs} = ROWS.map(|row| {body});';assert old in s;s=s.replace(old,f'let {lhs} = ['+','.join(re.sub(r'\brow\b',str(i)+'usize',body)for i in range(2,9))+'];')
s=s.replace('[leading_low, full_low, internal_low].map(PreparedQm31Multiplier::new)','[PreparedQm31Multiplier::new(leading_low),PreparedQm31Multiplier::new(full_low),PreparedQm31Multiplier::new(internal_low)]')
s=s.replace('''[1usize, 9, 10]
        .into_iter()
        .fold(QM31::ZERO, |sum, row| sum.add(selectors.local[row]))''','''QM31::ZERO.add(selectors.local[1]).add(selectors.local[9]).add(selectors.local[10])''')
s=s.replace('''(2usize..=8).fold(QM31::ZERO, |sum, row| sum.add(selectors.local[row]))''','QM31::ZERO'+''.join(f'.add(selectors.local[{i}])'for i in range(2,9)))
# Unroll only the small, statically bounded for loops, in their original order.
for pat,count,startnum in [('0..POSEIDON2_WIDTH',16,0),('1..POSEIDON2_WIDTH',16,1),('0..RATE',8,0)]:
 needle=f'for lane in {pat} {{'
 while needle in s:
  a=s.index(needle);bs=s.index('{',a)+1;end=bs;depth=1
  while depth:depth+=(s[end]=='{')-(s[end]=='}');end+=1
  body=s[bs:end-1];s=s[:a]+'\n'.join(re.sub(r'\blane\b',str(i)+'usize',body)for i in range(startnum,count))+s[end:]
(P/'reference_poseidon.rs').write_text(s)
Path('evidence/pv-b3p6-20261028/reference-poseidon227-resume5.json').write_text(json.dumps(dict(source_sha256=hashlib.sha256(source.encode()).hexdigest(),constants_source_sha256=hashlib.sha256(constants.encode()).hexdigest(),reference_sha256=hashlib.sha256(s.encode()).hexdigest(),changes=['owned copy of helpers between lift and multilinear_evaluate','copy exact three private constant tables','fixed4 array constructors and maps in same order','fixed7 ROWS maps and ordered sums','unroll fixed8/fixed16 for loops'],laws_outstanding=True),indent=2)+'\n')
s=s.replace('qm31_m31_dot,qm31_pack_base4,qm31_sum_products3_prepared,','').replace('PreparedQm31Multiplier,CM31','CM31')
s='use crate::reference_field::{qm31_m31_dot,qm31_pack_base4,qm31_sum_products3_prepared,PreparedQm31Multiplier};\n'+s
s=re.sub(r'&((?:openings\.)?\w+)\[start\.\.start \+ 4\]',lambda m:'&['+','.join(f'{m[1]}[start+{i}]'for i in range(4))+']',s)
(P/'reference_poseidon.rs').write_text(s)
p=Path('evidence/pv-b3p6-20261028/reference-poseidon227-resume5.json');r=json.loads(p.read_text());r['reference_sha256']=hashlib.sha256(s.encode()).hexdigest();r['field_helper_change']='owned fixed3/fixed7 field helpers; four-element slices replaced by same-order four copied values';p.write_text(json.dumps(r,indent=2)+'\n')
# Isolate scalar raw-matrix dispatch before unrolling surrounding array writes.
pattern=r'match output \{\s*0 => 2 \* a \+ 3 \* b \+ c \+ d,\s*1 => a \+ 2 \* b \+ 3 \* c \+ d,\s*2 => a \+ b \+ 2 \* c \+ 3 \* d,\s*3 => 3 \* a \+ b \+ c \+ 2 \* d,\s*_ => unreachable!\(\),\s*\}'
s,n=re.subn(pattern,'raw_limb227(output,a,b,c,d)',s);assert n==2,n
s+='''
fn raw_limb227(output:usize,a:u64,b:u64,c:u64,d:u64)->u64 {
    match output {0=>2*a+3*b+c+d,1=>a+2*b+3*c+d,2=>a+b+2*c+3*d,3=>3*a+b+c+2*d,_=>unreachable!()}
}
'''
while True:
 matches=list(re.finditer(r'while (group|output|index|lane|limb) < (4|POSEIDON2_WIDTH) \{',s))
 if not matches:break
 m=matches[-1];var=m[1];count=4 if m[2]=='4' else 16
 starts=list(re.finditer(r'(?:let mut )?\b'+var+r'\s*=\s*(\d+)(?:usize)?;',s[:m.start()]));assert starts,(var,m.start());first=int(starts[-1][1])
 a=m.start();bs=s.index('{',a)+1;depth=1;end=bs
 while depth:depth+=(s[end]=='{')-(s[end]=='}');end+=1
 body=s[bs:end-1].replace(f'{var} += 1;','');s=s[:a]+'\n'.join(re.sub(r'\b'+var+r'\b',str(i)+'usize',body)for i in range(first,count))+s[end:]
(P/'reference_poseidon.rs').write_text(s)
p=Path('evidence/pv-b3p6-20261028/reference-poseidon227-resume5.json');r=json.loads(p.read_text());r['reference_sha256']=hashlib.sha256(s.encode()).hexdigest();r['fixed_loop_change']='unroll fixed4/fixed16 while loops from their original initial counter; isolate same scalar raw-matrix match';p.write_text(json.dumps(r,indent=2)+'\n')
# The monolithic unroll timed out in external_linear_lazy at 6.2 GiB. Split
# its algebra into the same ordered four-lane operations and final additions.
a=s.index('fn external_linear_lazy(');b=s.index('// Every row of the four-lane external matrix',a)
body='fn external_linear_lazy(state:&mut[QM31;16]) {\n'
for group in range(4):
 start=4*group
 body+='    { let input=['+','.join(f'state[{start+i}]'for i in range(4))+'];\n'
 body+='      let output=external_group227(input);\n'
 for i in range(4):body+=f'      state[{start+i}]=output[{i}];\n'
 body+='    }\n'
body+='    let sums=global_sums227(*state);\n'
for i in range(16):body+=f'    state[{i}]=add_global227(state[{i}],sums[{i%4}]);\n'
body+='}\n\n'
s=s[:a]+body+s[b:]
helpers='\nfn external_group227(state:[QM31;4])->[QM31;4] {\n'
helpers+='    let input=['+','.join(f'extension_limbs(state[{i}])'for i in range(4))+'];\n    [\n'
for output in range(4):
 helpers+='    extension_from_raw_limbs([\n'
 for limb in range(4):
  helpers+='      {'+' '.join(f'let {var}=u64::from(input[{i}][{limb}]);'for i,var in enumerate(['a','b','c','d']))+f' raw_limb227({output},a,b,c,d)'+'},\n'
 helpers+='    ]),\n'
helpers+='    ]\n}\nfn global_sums227(state:[QM31;16])->[[u64;4];4] {\n    [\n'
for column in range(4):
 helpers+='    ['+','.join(' + '.join(f'u64::from(extension_limbs(state[{4*g+column}])[{limb}])'for g in range(4))for limb in range(4))+'],\n'
helpers+='    ]\n}\nfn add_global227(value:QM31,sums:[u64;4])->QM31 {\n    let limbs=extension_limbs(value);\n    extension_from_raw_limbs(['+','.join(f'u64::from(limbs[{i}])+sums[{i}]'for i in range(4))+'])\n}\n'
s+=helpers
(P/'reference_poseidon.rs').write_text(s)
p=Path('evidence/pv-b3p6-20261028/reference-poseidon227-resume5.json');r=json.loads(p.read_text());r['reference_sha256']=hashlib.sha256(s.encode()).hexdigest();r['timeout_replacement']=dict(old_gate='aeneas227-resume5-projectedloops',old_exit=124,old_wall_seconds=300.225,old_peak_rss_kib=6211868,old_swaps=0,declaration='external_linear_lazy',replacement='external_group227,global_sums227,add_global227; exact raw per-row arithmetic and global addition order; group writes moved after four pure calculations on pre-copied group input, requiring frame law',caps_unchanged=True);p.write_text(json.dumps(r,indent=2)+'\n')
a=s.index('fn interpolate_three_constant_columns(');b=s.index('\nfn interpolated_full_pair(',a)
raw=source[source.index('fn interpolate_three_constant_columns('):source.index('\nfn interpolated_full_pair(')]
expr=raw[raw.index('output[lane] = ')+len('output[lane] = '):raw.index(';\n        lane += 1;')]
for column in range(3):expr=expr.replace(f'column{column}[lane]',f'column{column}')
new='''fn interpolate_three_constant_columns(weights:[QM31;3],column0:[u32;16],column1:[u32;16],column2:[u32;16])->[QM31;16] {
    let mut output=[QM31::ZERO;16];
'''
for i in range(16):new+=f'    output[{i}]=interpolate_column227(weights,column0[{i}],column1[{i}],column2[{i}]);\n'
new+='    output\n}\n'
s=s[:a]+new+s[b:]
s+='\nfn interpolate_column227(weights:[QM31;3],column0:u32,column1:u32,column2:u32)->QM31 {\n'+expr+'\n}\n'
(P/'reference_poseidon.rs').write_text(s)
p=Path('evidence/pv-b3p6-20261028/reference-poseidon227-resume5.json');r=json.loads(p.read_text());r['reference_sha256']=hashlib.sha256(s.encode()).hexdigest();r['interpolation_timeout_replacement']=dict(old_gate='aeneas227-resume5-projectedsplit',old_exit=124,old_wall_seconds=300.117,old_peak_rss_kib=4005596,old_swaps=0,declaration='interpolate_three_constant_columns',replacement='interpolate_column227 receives owned weights and three scalar constant limbs; exact original field expression, with fixed16 ordered caller',external_linear_lazy_passed_before_timeout=True,caps_unchanged=True);p.write_text(json.dumps(r,indent=2)+'\n')
