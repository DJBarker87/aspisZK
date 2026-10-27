from pathlib import Path
import difflib,json
D=Path('evidence/pv-route2-20261027'); P=D/'probes'; rows=[]
def patch(op,path,old,new,kind,callers):
    (D/'patches'/f'{op}.patch').write_text(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+path,tofile='b/'+path)))
    rows.append(dict(op=op,kind=kind,callers=callers,added=sum(x.startswith('+') and not x.startswith('+++') for x in (D/'patches'/f'{op}.patch').read_text().splitlines()),removed=sum(x.startswith('-') and not x.startswith('---') for x in (D/'patches'/f'{op}.patch').read_text().splitlines())))
field='use aspis_core::field::{M31,CM31,QM31,WideExact,P};\n'
# Retain the prepared, unapplied host-only compressor patch.
import shutil
shutil.copyfile('evidence/pv-extract-20261027/route-ii-op223.patch',D/'patches/223.patch')
old=Path('crates/aspis-statement/src/logup.rs').read_text(); body=(Path('evidence/pv-extract-20261027/route-ii-op223.patch').read_text().split('@@ -0,0 +1,14 @@\n')[1].split('--- a/')[0]); body='\n'.join(l[1:] for l in body.splitlines() if l.startswith('+'))+'\n'; body=body.replace('pub(crate) fn','pub fn');(P/'223.rs').write_text(body)
rows.append(dict(op=223,kind='prover-local',callers=['host_semantic::copy_endpoint_values'],added=18,removed=1))
path='crates/aspis-r1-cost-probe/src/ct_pole.rs';old=Path(path).read_text();start=old.index('    for (row, sides)');end=old.index('    clear\n',start)
new=old[:start]+'''    let mut row = 0usize;
    while row < values.len() {
        let active = masks[row >> 4] & (1 << (row & 15)) != 0;
        let mut side = 0usize;
        while side < 2 {
            let mut slot = 0usize;
            while slot < 2 {
                clear = keep_clear(clear, active, chi, values[row][side][slot]);
                slot += 1;
            }
            side += 1;
        }
        row += 1;
    }
'''+old[end:];patch(258,path,old,new,'in-place',['host_semantic::copy_poles_clear']);(P/'258.rs').write_text(new.replace('pub(crate)','pub'))
path='crates/aspis-r1-cost-probe/src/sampler.rs';old=Path(path).read_text();start=old.index('    let mut quotient:');end=old.index('    // After eight divisions',start)
new=old[:start]+'''    let mut quotient = [0u32; 8];
    let mut i = 0usize;
    while i < 8 {
        quotient[i] = u32::from_le_bytes([block[4*i],block[4*i+1],block[4*i+2],block[4*i+3]]);
        i += 1;
    }
    let mut digits = [0u32; 8];
    let mut d = 0usize;
    while d < 8 {
        let mut remainder = 0u64;
        let mut j = 8usize;
        while j > 0 {
            j -= 1;
            let dividend = (remainder << 32) | u64::from(quotient[j]);
            quotient[j] = (dividend / u64::from(P)) as u32;
            remainder = dividend % u64::from(P);
        }
        digits[d] = remainder as u32;
        d += 1;
    }

'''+old[end:]
new=new.replace('    debug_assert!(quotient[1..].iter().all(|&limb| limb == 0));','    let mut check = 1usize;\n    while check < 8 { debug_assert!(quotient[check] == 0); check += 1; }')
new=new.replace('    for digit in digits {\n        let sum = u64::from(*digit) + u64::from(addend);\n        *digit = (sum % u64::from(P)) as u32;\n        addend = (sum / u64::from(P)) as u32;\n    }','    let mut i = 0usize;\n    while i < 8 {\n        let sum = u64::from(digits[i]) + u64::from(addend);\n        digits[i] = (sum % u64::from(P)) as u32;\n        addend = (sum / u64::from(P)) as u32;\n        i += 1;\n    }')
for op in [249,250]:
 patch(op,path,old,new,'in-place',['host_transcript::sample','transcript::sample','dense::sample']);probe=field+new[new.index('fn low_base_p_digits'):new.index('pub fn circle_sample')];(P/f'{op}.rs').write_text(probe)
path='crates/aspis-r1-cost-probe/src/weights.rs';old=Path(path).read_text();new=old.replace('  if i==N { return out; }\n  p=p.mul(x);','  if i<N { p=p.mul(x); }');patch(254,path,old,new,'in-place',['Weights::dual_raw','Weights::pair','Weights::materialize']);body=new[new.index('pub fn powers'):new.index('pub fn kpowers')];(P/'254.rs').write_text(field+'use aspis_core::field::WideExact as E;\n'+body)
path='crates/aspis-statement/src/state_only_semantic.rs';old=Path(path).read_text();needle='    (h1.len() == TRACE_ROWS).then(|| h1.iter().copied().fold(QM31::ZERO, QM31::add))';replacement='''    if h1.len() == TRACE_ROWS {
        let mut sum = QM31::ZERO;
        let mut i = 0usize;
        while i < h1.len() { sum = sum.add(h1[i]); i += 1; }
        Some(sum)
    } else { None }''';new=old.replace(needle,replacement);body=new[new.index('pub fn state_only_copy_helper_sum'):new.index('\n#[cfg(test)]',new.index('pub fn state_only_copy_helper_sum'))];local='crates/aspis-r1-cost-probe/src/prover_helper_sum.rs';patch(230,local,'',field+'const TRACE_ROWS:usize=1024;\n'+body,'prover-local',['host_semantic copy helper consumers (redirect required)']);(P/'230.rs').write_text(field+'const TRACE_ROWS:usize=1024;\n'+body)
(D/'candidates.json').write_text(json.dumps(rows,indent=2)+'\n')
