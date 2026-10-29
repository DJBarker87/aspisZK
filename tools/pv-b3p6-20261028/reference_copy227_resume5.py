"""Generate owned copy-helper candidate; preserve deployed arithmetic order."""
from pathlib import Path
import json,hashlib
P=Path('tools/pv-b3p6-20261028/v244');s=(P/'host_copy_terminal.rs').read_text()
a=s.index('        limb = 0;\n        while limb < POSEIDON2_WIDTH {',s.index('fn pattern_values_literal'))
b=s.index('        result[pattern_index] = value;',a)
old=s[a:b]
s=s[:a]+'''        limb = 0;
        while limb < POSEIDON2_WIDTH {
            value = pattern_limb227(pattern,limb,*openings,powers,value);
            limb += 1;
        }
'''+s[b:]
s+='''
fn pattern_limb227(pattern:CompiledPoolV1PairForestPattern,limb:usize,openings:[QM31;16],powers:[QM31;16],value:QM31)->QM31 {
    if pattern.kinds[limb]==1 {
        let source=openings[usize::from(pattern.columns[limb])].add(lift_m31(M31(pattern.offsets[limb])));
        value.add(powers[limb].mul(source))
    } else {value}
}
'''
(P/'reference_copy_terminal.rs').write_text(s)
Path('evidence/pv-b3p6-20261028/reference-copy227-resume5.json').write_text(json.dumps(dict(source_sha256=hashlib.sha256((P/'host_copy_terminal.rs').read_bytes()).hexdigest(),reference_sha256=hashlib.sha256(s.encode()).hexdigest(),original_inner_loop=old,change='isolate limb branch in owned value helper, preserves indexing inside kind==1 and field operations/order',proved=False),indent=2)+'\n')
a=s.index('    fn active_literal(&self)');b=s.index('\n    #[cfg',a);part=s[a:b]
a0=part.index('            let mask =');b0=part.index('            block += 1;',a0)
part=part[:a0]+'            sum=active_block227(*self,block,sum);\n'+part[b0:]
s=s[:a]+part+s[b:]
s+='''
fn active_block227(selectors:Selectors,block:usize,sum:QM31)->QM31 {
    let mask=constants::ACTIVE_ROW_MASKS[block];
    if mask!=0 { sum.add(selectors.high[block].mul(selector_mask_sum_16(selectors.low,mask))) } else {sum}
}
'''
s=s.replace('fn selector_mask_sum_16(values: &[QM31; 16],','fn selector_mask_sum_16(values: [QM31; 16],')
s=s.replace('''sum = if complement {
            sum.sub(values[index])
        } else {
            sum.add(values[index])
        };''','''sum = mask_step227(values,index,sum,complement);''')
s+='''
fn mask_step227(values:[QM31;16],index:usize,sum:QM31,complement:bool)->QM31 {
    if complement {sum.sub(values[index])} else {sum.add(values[index])}
}
'''
(P/'reference_copy_terminal.rs').write_text(s)
p=Path('evidence/pv-b3p6-20261028/reference-copy227-resume5.json');r=json.loads(p.read_text());r['reference_sha256']=hashlib.sha256(s.encode()).hexdigest();r['active_change']='active_block227 owns selector copy; mask_step227 owns values and isolates scalar add/sub branch; unchanged guard and operation order';p.write_text(json.dumps(r,indent=2)+'\n')
import re
text=(P/'host_copy_terminal_constants.rs').read_text();m=re.search(r'const ACTIVE_ROW_MASKS: \[u16; 64\] = \[([^]]+)\]',text);assert m
masks=[int(v.strip())for v in m[1].split(',')if v.strip()];assert len(masks)==64
unique=sorted(set(masks));assert all(mask.bit_count()<=8 for mask in unique)
a=s.index('fn selector_mask_sum_16(');b=s.index('\n#[derive',a)
new='fn selector_mask_sum_16(values:[QM31;16],mask:u16)->QM31 {\n    match mask {\n'
for mask in unique:
    bits=[i for i in range(16)if mask&(1<<i)]
    new+=f'        {mask} => QM31::ZERO'+''.join(f'.add(values[{i}])'for i in bits)+',\n'
new+='        _ => panic!("outside frozen active mask set"),\n    }\n}\n'
s=s[:a]+new+s[b:]
(P/'reference_copy_terminal.rs').write_text(s)
p=Path('evidence/pv-b3p6-20261028/reference-copy227-resume5.json');r=json.loads(p.read_text());r['reference_sha256']=hashlib.sha256(s.encode()).hexdigest();r['mask_specialization']=dict(all64_masks=masks,unique_masks=unique,popcounts={str(mask):mask.bit_count()for mask in unique},calls='only active_block227 with frozen mask table indexed before call',branch='all reached masks have count_ones<=8, so original complement=false',order='ZERO followed by additions at increasing set-bit indices, exactly repeated trailing_zeros/clear-lowest-bit traversal',default='unreachable on frozen64 table; Lean law outstanding');p.write_text(json.dumps(r,indent=2)+'\n')
