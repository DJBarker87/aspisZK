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
