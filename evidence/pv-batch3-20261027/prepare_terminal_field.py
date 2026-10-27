from pathlib import Path
R=Path(__file__).resolve().parents[2];D=R/'crates/aspis-r1-cost-probe/src'
a=(R/'crates/aspis-prover/src/host_arithmetic.rs').read_text()
# Reuse exact already Drop-free helper bodies, in a new gated private module.
prep=a[a.index('#[derive(Clone, Copy)]\nstruct PreparedQm31Multiplier'):a.index('#[inline(always)]\nfn reconstruct_component')]
prep=prep.replace('struct PreparedQm31Multiplier','pub(crate) struct PreparedQm31Multiplier').replace('    fn new(', '    pub(crate) fn new(').replace('    fn mul(', '    pub(crate) fn mul(')
component=a[a.index('#[inline(always)]\nfn reconstruct_component'):a.index('#[inline(always)]\nfn qm31_sum_products3')]
base='''//! Gated terminal arithmetic helpers; same field operation and accumulation order.\nuse aspis_core::field::{M31, CM31, QM31, P};\n#[inline(always)]\nfn cm31_mul_r(value: CM31) -> CM31 {\n    CM31::new(value.a.double().sub(value.b), value.a.add(value.b.double()))\n}\n'''+prep+component
for n in [2,3,4]:
 base+=f'''\n#[inline(always)]\npub(crate) fn qm31_sum_products{n}(left: [QM31; {n}], right: [QM31; {n}]) -> QM31 {{\n    let sums = [[0u64; 3]; 3];\n'''
 for i in range(n):base+=f'    let sums = accumulate_channels(sums, left[{i}], right[{i}]);\n'
 base+='    reconstruct_channels(sums)\n}\n'
f=(R/'crates/aspis-core/src/field.rs').read_text();start=f.index('pub fn qm31_pack_base4(');end=f.index('\n}\n',start)+3;s=f[start:end]
s=s.replace('pub fn ','pub(crate) fn ',1).replace('    padded[..values.len()].copy_from_slice(values);','    let mut i = 0usize;\n    while i < values.len() { padded[i] = values[i]; i += 1; }').replace('    let limb = |value: M31| u64::from(value.0);','')
s=s.replace('limb(', 'terminal_limb(')
base+='\n#[inline(always)]\nfn terminal_limb(value: M31) -> u64 { u64::from(value.0) }\n\n#[inline(always)]\n'+s
(D/'host_terminal_field.rs').write_text(base)
p=D/'lib.rs';s=p.read_text();s+='\n#[cfg(feature = "prover")]\nmod host_terminal_field;\n';p.write_text(s)
p=D/'host_terminal.rs';s=p.read_text().replace('field::{qm31_pack_base4, PreparedQm31Multiplier, CM31, M31, QM31}', 'field::{CM31, M31, QM31}')
s=s.replace('use aspis_core::{','use crate::host_terminal_field::{qm31_pack_base4, PreparedQm31Multiplier};\nuse aspis_core::{',1)
s=s.replace('    constants::POOL_V1_PAIR_EMPTY_ROOTS_V1[level].map(M31)','    let words = constants::POOL_V1_PAIR_EMPTY_ROOTS_V1[level];\n    [M31(words[0]), M31(words[1]), M31(words[2]), M31(words[3]),\n     M31(words[4]), M31(words[5]), M31(words[6]), M31(words[7])]')
p.write_text(s)
p=D/'host_copy_terminal.rs';s=p.read_text().replace('use aspis_core::field::{qm31_sum_products2, qm31_sum_products3, qm31_sum_products4};','use crate::host_terminal_field::{qm31_sum_products2, qm31_sum_products3, qm31_sum_products4};').replace('use aspis_core::field::{PreparedQm31Multiplier, CM31, M31, QM31};','use crate::host_terminal_field::PreparedQm31Multiplier;\nuse aspis_core::field::{CM31, M31, QM31};')
a=s.index('    fn expand<const N: usize>');b=s.index('\n    #[inline(never)]',a)
s=s[:a]+'''    fn expand<const N: usize>(point: &[QM31; 10], start: usize, count: usize) -> [QM31; N] {
        let mut weights = [QM31::ZERO; N];
        weights[0] = QM31::ONE;
        let mut len = 1usize;
        let mut coordinate = start;
        while coordinate < start + count {
            let prepared = PreparedQm31Multiplier::new(point[coordinate]);
            let mut index = len;
            while index > 0 {
                index -= 1;
                let parent = weights[index];
                let right = prepared.mul(parent);
                weights[2 * index] = parent.sub(right);
                weights[2 * index + 1] = right;
            }
            len *= 2;
            coordinate += 1;
        }
        weights
    }

    pub(crate) fn at_point(point: &[QM31; 10]) -> Self {
        Self { high: Self::expand(point, 0, 6), low: Self::expand(point, 6, 4) }
    }
'''+s[b:];p.write_text(s)
p=R/'evidence/pv-batch3-20261027/extract-copies/lib.rs';s=p.read_text();s+='\n#[path="../../../crates/aspis-r1-cost-probe/src/host_terminal_field.rs"]\nmod host_terminal_field;\n';p.write_text(s)
