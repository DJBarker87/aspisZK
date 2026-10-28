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
