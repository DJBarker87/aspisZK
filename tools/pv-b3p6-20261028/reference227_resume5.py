"""Generate an owned iterator-free candidate; shipped bytes remain frozen."""
from pathlib import Path
import hashlib,json
P=Path('tools/pv-b3p6-20261028/v244');s=(P/'host_terminal.rs').read_text();edits=[]
def replace(a,b):
 global s
 assert s.count(a)==1,a
 s=s.replace(a,b);edits.append(dict(before=a,after=b))
replace('''    for range in ranges {
        for block in range.clone() {
            sum = sum.add(selectors.high[block]);
        }
    }''','''    let mut range_index = 0usize;
    while range_index < ranges.len() {
        let mut block = ranges[range_index].start;
        while block < ranges[range_index].end {
            sum = sum.add(selectors.high[block]);
            block += 1;
        }
        range_index += 1;
    }''')
replace('''        for residual in &mut range {
            *residual = range_selector.mul(*residual);
        }''','''        let mut residual_index = 0usize;
        while residual_index < 33 {
            range[residual_index] = range_selector.mul(range[residual_index]);
            residual_index += 1;
        }''')
(P/'reference_terminal.rs').write_text(s)
record=dict(candidate_only=True,source='host_terminal.rs',source_sha256=hashlib.sha256((P/'host_terminal.rs').read_bytes()).hexdigest(),reference='reference_terminal.rs',reference_sha256=hashlib.sha256(s.encode()).hexdigest(),edits=edits,remaining='prove loop equivalences in Lean and complete Result law; native validation; source correspondence not yet established')
Path('evidence/pv-b3p6-20261028/reference227-resume5.json').write_text(json.dumps(record,indent=2)+'\n')
s=s.replace('struct SemanticPublic {','pub struct SemanticPublic {')
s+='''
fn claim227(claims: [[QM31;29];3], index: usize) -> QM31 { let row=claims[index/28]; row[index%28] }

/// Owned value entry: copy the immutable inputs before evaluating the same chain.
pub fn reference227(public: SemanticPublic, claims: [[QM31;29];3], alpha: [QM31;10], c: aspis_core::state_only_prefix::r0::Challenges) -> Result<QM31,aspis_core::state_only_prefix::r0::Error> {
    let mut selected=[QM31::ZERO;84];
    let mut i=0usize;
    while i<84 { let value=claim227(claims,i); selected[i]=value; i+=1; }
    match terminal_parts(public,&selected,&alpha,c.lambda,c.chi,c.theta,&c.zc,c.mu) {
        Ok(parts)=>Ok(parts.0),
        Err(_)=>Err(aspis_core::state_only_prefix::r0::Error::Public)
    }
}
'''
(P/'reference_terminal.rs').write_text(s)
record['reference_sha256']=hashlib.sha256(s.encode()).hexdigest()
record['entry_change']='owned SemanticPublic, owned immutable claims/alpha/Challenges; same selected84 fill and terminal_parts Result mapping; conversion law outstanding'
Path('evidence/pv-b3p6-20261028/reference227-resume5.json').write_text(json.dumps(record,indent=2)+'\n')
s=s.replace('semantic[index]', 'read227(semantic,index)').replace('poseidon[index]', 'read227(poseidon,index)')
s+='\nfn read227<const N:usize>(values:[QM31;N], index:usize)->QM31 { values[index] }\n'
(P/'reference_terminal.rs').write_text(s)
record['reference_sha256']=hashlib.sha256(s.encode()).hexdigest()
record['array_read_change']='semantic/poseidon reverse-Horner loop reads via owned-copy read227; read identity law outstanding'
Path('evidence/pv-b3p6-20261028/reference227-resume5.json').write_text(json.dumps(record,indent=2)+'\n')
s=s.replace('equality_factor(left[index], right[index])', 'equality_factor(read227(*left,index), read227(*right,index))')
(P/'reference_terminal.rs').write_text(s)
record['reference_sha256']=hashlib.sha256(s.encode()).hexdigest()
record['equality_read_change']='equality_value loop reads via owned-copy read227'
Path('evidence/pv-b3p6-20261028/reference227-resume5.json').write_text(json.dumps(record,indent=2)+'\n')
a=s.index('fn equality_value(');b=s.index('\n#[allow(clippy::type_complexity)]',a)
s=s[:a]+'''fn equality_value(left: &[QM31;10], right: &[QM31;10]) -> QM31 {
    let mut product=equality_factor(left[0],right[0]);
'''+''.join(f'    product=product.mul(equality_factor(left[{i}],right[{i}]));\n' for i in range(1,10))+'''    product
}
'''+s[b:]
(P/'reference_terminal.rs').write_text(s)
record['reference_sha256']=hashlib.sha256(s.encode()).hexdigest()
record['equality_read_change']='ten equality factors unrolled in original order; loop/unroll law outstanding'
Path('evidence/pv-b3p6-20261028/reference227-resume5.json').write_text(json.dumps(record,indent=2)+'\n')
# Preserve exact order, including continue edges, with increment before the body.
import re
s=re.sub(r'for (level|lane|group) in (0\.\.20|0\.\.DIGEST_ELEMS|first\.\.=last) \{',lambda m:(f'let mut {m[1]}_index = '+('first' if m[2]=='first..=last' else '0usize')+f'; while {m[1]}_index '+('<= last' if m[2]=='first..=last' else '< '+('20' if m[2]=='0..20' else 'DIGEST_ELEMS'))+f' {{ let {m[1]}={m[1]}_index; {m[1]}_index+=1;'),s)
s=s.replace('source.frontier[level]','digest227(source.frontier,level)').replace('after.next_frontier[level]','digest227(after.next_frontier,level)')
s+='\nfn digest227(values:[Digest;20],index:usize)->Digest { values[index] }\n'
(P/'reference_terminal.rs').write_text(s)
record['reference_sha256']=hashlib.sha256(s.encode()).hexdigest()
record['range_change']='level/lane/group range iteration replaced by increasing index while; increments before body preserve continue; fixed reached bounds; laws outstanding'
Path('evidence/pv-b3p6-20261028/reference227-resume5.json').write_text(json.dumps(record,indent=2)+'\n')
s=s.replace('sum_high(selectors, &[0..57])','sum_interval227(selectors.high,QM31::ZERO,0,57)')
s=s.replace('sum_high(selectors, &[4..25, 33..57])','sum_interval227(selectors.high,sum_interval227(selectors.high,QM31::ZERO,4,25),33,57)')
s=s.replace('sum_high(selectors, &[57..63])','sum_interval227(selectors.high,QM31::ZERO,57,63)')
s+='''
fn sum_interval227(high:[QM31;64], initial:QM31, start:usize, end:usize)->QM31 {
    let mut sum=initial;
    let mut i=start;
    while i<end { sum=sum.add(read227(high,i)); i+=1; }
    sum
}
'''
(P/'reference_terminal.rs').write_text(s)
record['reference_sha256']=hashlib.sha256(s.encode()).hexdigest()
record['sum_change']='three fixed range lists specialized to ordered sum_interval227 calls with previous sum threaded; no reassociation'
Path('evidence/pv-b3p6-20261028/reference227-resume5.json').write_text(json.dumps(record,indent=2)+'\n')
for field in ['z','succ_z','xor12_z']:
    s=s.replace(f'openings.{field}[index]',f'read227(openings.{field},index)')
s=s.replace('range_selector.mul(range[residual_index])','range_selector.mul(read227(range,residual_index))')
(P/'reference_terminal.rs').write_text(s)
record['reference_sha256']=hashlib.sha256(s.encode()).hexdigest()
record['value_read_change']='value lane loop reads through owned-array read227; mutation order unchanged'
Path('evidence/pv-b3p6-20261028/reference227-resume5.json').write_text(json.dumps(record,indent=2)+'\n')
a=s.index('fn add_value_lanes(');b=s.index('\n#[inline(never)]\nfn variant_expected_output',a);part=s[a:b]
for var,count in [('index',10),('residual_index',33)]:
    while f'while {var} < {count} {{' in part:
        start=part.index(f'while {var} < {count} {{');body_start=part.index('{',start)+1;depth=1;end=body_start
        while depth:
            depth+=(part[end]=='{')-(part[end]=='}');end+=1
        body=part[body_start:end-1].replace(f'{var} += 1;','')
        expanded='\n'.join(re.sub(r'\b'+var+r'\b',str(i)+'usize',body) for i in range(count))
        part=part[:start]+expanded+part[end:]
s=s[:a]+part+s[b:]
(P/'reference_terminal.rs').write_text(s)
record['reference_sha256']=hashlib.sha256(s.encode()).hexdigest()
record['value_loop_change']='three length10 value residual loops and length33 weighting loop unrolled in increasing order; no field reassociation; laws outstanding'
Path('evidence/pv-b3p6-20261028/reference227-resume5.json').write_text(json.dumps(record,indent=2)+'\n')
a=s.index('fn public_digest_lanes(');b=s.index('/// Audit-only form',a);part=s[a:b]
needle='while level_index < 20 {'
start=part.index(needle);bs=part.index('{',start)+1;depth=1;end=bs
while depth:
    depth+=(part[end]=='{')-(part[end]=='}');end+=1
body=part[bs:end-1].replace('let level=level_index; level_index+=1;','')
part=part[:start]+'\n'.join(re.sub(r'\blevel\b',str(i)+'usize',body)for i in range(20))+part[end:]
s=s[:a]+part+s[b:]
(P/'reference_terminal.rs').write_text(s)
record['reference_sha256']=hashlib.sha256(s.encode()).hexdigest()
record['digest_loop_change']='public_digest_lanes fixed20 loop unrolled with branch/selector/call order preserved; law outstanding'
Path('evidence/pv-b3p6-20261028/reference227-resume5.json').write_text(json.dumps(record,indent=2)+'\n')
a=s.index('fn add_digest_binding(');b=s.index('\n#[inline(never)]',a);part=s[a:b]
part=part.replace('output: &mut [QM31; DIGEST_ELEMS]','mut output: [QM31; DIGEST_ELEMS]').replace('opened: &[QM31; POSEIDON2_WIDTH]','opened: [QM31; POSEIDON2_WIDTH]').replace('expected: &Digest','expected: Digest').replace(') {',') -> [QM31;DIGEST_ELEMS] {',1)
part=part.rstrip();assert part.endswith('}');part=part[:-1]+'    output\n}\n'
s=s[:a]+part+s[b:]
a=s.index('fn public_digest_lanes(');b=s.index('/// Audit-only form',a);part=s[a:b]
part=part.replace('openings: &StateOnlyPoseidonOpenings','openings: StateOnlyPoseidonOpenings').replace('selectors: &Selectors','selectors: Selectors')
part=part.replace('add_digest_binding(','digests = add_digest_binding(').replace('&mut digests,','digests,')
part=re.sub(r'&(openings\.z|public\.anchor|public\.nullifier|recipient|public\.change|after\.next_root|after\.next_frontier\[carry\]|empty_root\([^)]*\)|digest227\([^)]*\))',r'\1',part)
s=s[:a]+part+s[b:]
s=s.replace('public_digest_lanes(public, openings, selectors)','public_digest_lanes(public, *openings, *selectors)')
(P/'reference_terminal.rs').write_text(s)
record['reference_sha256']=hashlib.sha256(s.encode()).hexdigest()
record['digest_state_change']='digest helper threads owned output value and immutable copied opened/expected values; public digest copies openings/selectors; all same calls/order and branch guards; state/value law outstanding'
Path('evidence/pv-b3p6-20261028/reference227-resume5.json').write_text(json.dumps(record,indent=2)+'\n')
# Specialize fixed array constructors, retaining each body evaluation exactly once.
for size in [16,4]:
    arm=f'''    ({size}, $index:ident, $body:expr) => {{{{
        let mut output=[QM31::ZERO;{size}];
'''+''.join(f'        {{ let $index={i}usize; output[{i}]=$body; }}\n' for i in range(size))+'''        output
    }};
'''
    s=s.replace('macro_rules! qm31_array {','macro_rules! qm31_array {\n'+arm,1)
(P/'reference_terminal.rs').write_text(s)
record['reference_sha256']=hashlib.sha256(s.encode()).hexdigest()
record['constructor_change']='fixed16/fixed4 qm31_array arms unrolled in exact index order; generic arm unchanged; law outstanding'
Path('evidence/pv-b3p6-20261028/reference227-resume5.json').write_text(json.dumps(record,indent=2)+'\n')
a=s.index('fn semantic_initial_and_absorption(');b=s.index('\n#[cfg(any(test, not(feature = "optimized-terminal")))]',a);part=s[a:b]
part=part.replace('openings: &StateOnlyPoseidonOpenings','openings: StateOnlyPoseidonOpenings').replace('selectors: &Selectors','selectors: Selectors').replace('openings.z[lane]','read227(openings.z,lane)')
s=s[:a]+part+s[b:]
s=s.replace('semantic_initial_and_absorption(public, openings, selectors)','semantic_initial_and_absorption(public, *openings, *selectors)')
(P/'reference_terminal.rs').write_text(s)
record['reference_sha256']=hashlib.sha256(s.encode()).hexdigest()
record['initial_state_change']='semantic_initial_and_absorption copies immutable openings/selectors and reads via owned-array helper'
Path('evidence/pv-b3p6-20261028/reference227-resume5.json').write_text(json.dumps(record,indent=2)+'\n')
a='''if lane < RATE {
            full_or_rate.mul(read227(openings.z,lane))
        } else {
            full.mul(read227(openings.z,lane))
        }'''
assert s.count(a)==1
s=s.replace(a,'initial_lane227(lane,full_or_rate,full,read227(openings.z,lane))')
s+='''
fn initial_lane227(lane:usize,full_or_rate:PreparedQm31Multiplier,full:PreparedQm31Multiplier,value:QM31)->QM31 {
    if lane<RATE { full_or_rate.mul(value) } else { full.mul(value) }
}
'''
(P/'reference_terminal.rs').write_text(s)
record['reference_sha256']=hashlib.sha256(s.encode()).hexdigest()
record['initial_branch_change']='scalar initial_lane227 helper isolates identical lane<RATE branch, preserving selected multiplication'
Path('evidence/pv-b3p6-20261028/reference227-resume5.json').write_text(json.dumps(record,indent=2)+'\n')
needle='while lane_index < DIGEST_ELEMS {'
while needle in s:
    start=s.index(needle);bs=s.index('{',start)+1;depth=1;end=bs
    while depth:
        depth+=(s[end]=='{')-(s[end]=='}');end+=1
    body=s[bs:end-1].replace('let lane=lane_index; lane_index+=1;','')
    s=s[:start]+'\n'.join(re.sub(r'\blane\b',str(i)+'usize',body)for i in range(8))+s[end:]
(P/'reference_terminal.rs').write_text(s)
record['reference_sha256']=hashlib.sha256(s.encode()).hexdigest()
record['lane_loop_change']='all fixed8 source lane loops unrolled in increasing order; paths/occupancy/digest output writes preserved'
Path('evidence/pv-b3p6-20261028/reference227-resume5.json').write_text(json.dumps(record,indent=2)+'\n')
a=s.index('fn reconstruct_10(');b=s.index('\nfn ',a+3);part=s[a:b]
needle='while index > 0 {';start=part.index(needle);bs=part.index('{',start)+1;depth=1;end=bs
while depth:
    depth+=(part[end]=='{')-(part[end]=='}');end+=1
body=part[bs:end-1].replace('index -= 1;','')
part=part[:start]+'\n'.join(re.sub(r'\bindex\b',str(i)+'usize',body)for i in reversed(range(9)))+part[end:]
s=s[:a]+part+s[b:]
(P/'reference_terminal.rs').write_text(s)
record['reference_sha256']=hashlib.sha256(s.encode()).hexdigest()
record['reconstruct_change']='reconstruct_10 reverse loop unrolled for indices8 through0 in unchanged order'
Path('evidence/pv-b3p6-20261028/reference227-resume5.json').write_text(json.dumps(record,indent=2)+'\n')
a=s.index('fn add_digest_binding(');b=s.index('\n#[inline(never)]',a);part=s[a:b]
part,count=re.subn(r'let mut target = expected\[(\d+usize)\];\s*if right_tweak && \1 \+ 1 == DIGEST_ELEMS \{\s*target = target.add\(MERKLE_NODE_COMPRESSION_V3_TWEAK\);\s*\}',r'let target=tweak227(expected[\1],right_tweak,\1);',part)
assert count==8,count
s=s[:a]+part+s[b:]
s+='''
fn tweak227(value:M31,right_tweak:bool,lane:usize)->M31 {
    if right_tweak && lane+1==DIGEST_ELEMS { value.add(MERKLE_NODE_COMPRESSION_V3_TWEAK) } else { value }
}
'''
(P/'reference_terminal.rs').write_text(s)
record['reference_sha256']=hashlib.sha256(s.encode()).hexdigest()
record['digest_branch_change']='scalar tweak227 helper isolates same right_tweak/lane guard and optional M31 addition'
Path('evidence/pv-b3p6-20261028/reference227-resume5.json').write_text(json.dumps(record,indent=2)+'\n')
s=s.replace('crate::host_copy_terminal::','crate::reference_copy_terminal::')
(P/'reference_terminal.rs').write_text(s)
record['reference_sha256']=hashlib.sha256(s.encode()).hexdigest()
record['copy_helper_change']='use owned reference_copy_terminal; see reference-copy227-resume5.json'
Path('evidence/pv-b3p6-20261028/reference227-resume5.json').write_text(json.dumps(record,indent=2)+'\n')
old='''    let mut selected=[QM31::ZERO;84];
    let mut i=0usize;
    while i<84 { let value=claim227(claims,i); selected[i]=value; i+=1; }
'''
assert s.count(old)==1
s=s.replace(old,'    let selected=select227(claims);\n')
s+='\npub fn select227(claims:[[QM31;29];3])->[QM31;84] {\n'+old+'    selected\n}\n'
(P/'reference_terminal.rs').write_text(s)
record['reference_sha256']=hashlib.sha256(s.encode()).hexdigest()
record['selection_change']='factor unchanged owned select84 loop into select227 for a focused complete selection proof'
Path('evidence/pv-b3p6-20261028/reference227-resume5.json').write_text(json.dumps(record,indent=2)+'\n')
old='''        let blocks = if lane < 2 {
            fixed
        } else if lane < RATE {
            fixed.add(chunk_two)
        } else {
            fixed.add(chunk_two).add(chunk_eight).add(nodes)
        };
        low.mul(blocks).mul(openings[lane])'''
assert s.count(old)==1
s=s.replace(old,'        absorption_lane227(lane,low,fixed,chunk_two,chunk_eight,nodes,read227(*openings,lane))')
s+='''
fn absorption_lane227(lane:usize,low:QM31,fixed:QM31,chunk_two:QM31,chunk_eight:QM31,nodes:QM31,opened:QM31)->QM31 {
    let blocks=if lane<2 {fixed} else if lane<RATE {fixed.add(chunk_two)} else {fixed.add(chunk_two).add(chunk_eight).add(nodes)};
    low.mul(blocks).mul(opened)
}
'''
(P/'reference_terminal.rs').write_text(s)
record['reference_sha256']=hashlib.sha256(s.encode()).hexdigest()
record['absorption_change']='scalar absorption_lane227 isolates unchanged three-way lane branch and arithmetic chain'
Path('evidence/pv-b3p6-20261028/reference227-resume5.json').write_text(json.dumps(record,indent=2)+'\n')
s=s.replace('source.next_pair_index.checked_add(1) != Some(after.next_pair_index)','checked_next227(source.next_pair_index,after.next_pair_index)')
s+='\nfn checked_next227(index:u64,next:u64)->bool { match index.checked_add(1) { Some(value)=>value!=next,None=>true } }\n'
(P/'reference_terminal.rs').write_text(s)
record['reference_sha256']=hashlib.sha256(s.encode()).hexdigest()
record['option_change']='checked_next227 explicitly matches checked_add result instead of Option inequality; scalar law outstanding'
Path('evidence/pv-b3p6-20261028/reference227-resume5.json').write_text(json.dumps(record,indent=2)+'\n')
s=s.replace('evaluate_state_only_poseidon_oracle_projected, StateOnlyPoseidonOpenings,','StateOnlyPoseidonOpenings,')
s=s+'\nuse crate::reference_poseidon::evaluate_state_only_poseidon_oracle_projected;\n'
(P/'reference_terminal.rs').write_text(s)
record['reference_sha256']=hashlib.sha256(s.encode()).hexdigest()
record['poseidon_change']='owned projected Poseidon copy; source and structural change records in reference-poseidon227-resume5.json and reference-field227-resume5.json'
Path('evidence/pv-b3p6-20261028/reference227-resume5.json').write_text(json.dumps(record,indent=2)+'\n')
s=s.replace('        fn semantic(self) -> SemanticPublic {','        pub(super) fn semantic(self) -> SemanticPublic {')
s+='''
pub fn native227(public:r0::Public<'_>,claims:&[[QM31;29];3],alpha:&[QM31;10],c:&aspis_core::state_only_prefix::r0::Challenges)->Result<QM31,aspis_core::state_only_prefix::r0::Error> {
    reference227(public.semantic(),*claims,*alpha,*c)
}
'''
(P/'reference_terminal.rs').write_text(s)
record['reference_sha256']=hashlib.sha256(s.encode()).hexdigest()
record['native_entry']='copy public.semantic/claims/alpha/challenges into owned entry; semantic visibility only widened within parent'
Path('evidence/pv-b3p6-20261028/reference227-resume5.json').write_text(json.dumps(record,indent=2)+'\n')
