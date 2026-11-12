#!/usr/bin/env python3
"""X1b item K: iterator adapters of the on-chain emission that the native `Iterator` structure lacks (`rev`, `fold`,
`any`, `contains` on a range, `into_iter().fold` on an array), written as counted `while` loops or as the expression
they compute, with the same operations in the same order and the same values. Line-preserving (no line added or
removed). Not rewritten here, and why: `merkle_verdict` (`chunks_exact(8).any`: a data-dependent tail length; every
rewrite found adds per-byte work or a bounds check per word), the `core::array::map` sites (not an iterator method),
and `semantic.into_iter().rev()` in pair_forest_semantic_terminal.rs 2055 and 2058 (not in the on-chain emission).
usage: fv_x1b_rwK.py <tree>   (edits the tree in place; refuses the frozen tree)"""
import sys
from pathlib import Path
T = Path(sys.argv[1]); assert 'src-frz-a' not in str(T)

def sub(path, old, new, after=None):
    p = T / path; t = p.read_text()
    a = t.index(after) if after else 0
    head, tail = t[:a], t[a:]
    assert (tail.count(old) >= 1 if after else t.count(old) == 1), (path, old, t.count(old))
    assert len(new.split('\n')) == len(old.split('\n')), ('line count', path, old)
    p.write_text(head + tail.replace(old, new, 1))

V = 'crates/aspis-r1-cost-probe/src/'
# K1 parse_shape, parse_packed_shape: `any nonzero byte` of the 7 tail bytes is `the 7 bytes differ from zero`
sub(V + 'candidate.rs', '        || proof[9..16].iter().any(|&x| x != 0)\n    {\n        return Err(Error::Parse);\n    }\n    Ok(Variant::S2)',
    '        || proof[9..16] != [0u8; 7]\n    {\n        return Err(Error::Parse);\n    }\n    Ok(Variant::S2)')
sub(V + 'one_tx.rs', '        || proof[9..16].iter().any(|&x| x != 0)\n',
    '        || proof[9..16] != [0u8; 7]\n')
# K2 Weights::scalar_factor: the four-term fold as a counted loop, same terms in the same order
sub(V + 'weights.rs', '        (0..4).fold(E::ZERO,|v,s|v.add(p[PERM[s]].mul_qm31(f[s]))).mul_m31(QUARTER)',
    '        {let mut v=E::ZERO;let mut s=0;while s<4 {v=v.add(p[PERM[s]].mul_qm31(f[s]));s+=1;} v}.mul_m31(QUARTER)')
# K3 polynomial: Horner over i = 6, 5, ..., 0
sub(V + 'verifier.rs', 'pub fn polynomial(bytes:&[u8],x:E)->E {(0..7).rev().fold(E::ZERO,|a,i|a.mul(x).add(field(bytes,i)))}',
    'pub fn polynomial(bytes:&[u8],x:E)->E {let mut a=E::ZERO;let mut i=7;while i>0 {i-=1;a=a.mul(x).add(field(bytes,i));} a}')
# K4 the program crate: the lane header tail and the close-checkpoint seed length
sub('programs/r1-cost-probe/src/r1_pool_adapter.rs', '''        || bytes[73..POOL_V1_PAIR_FOREST_LANE_HEADER_BYTES]
            .iter()
            .any(|byte| *byte != 0)''', '''        || bytes[73..POOL_V1_PAIR_FOREST_LANE_HEADER_BYTES]
            !=
            [0u8; POOL_V1_PAIR_FOREST_LANE_HEADER_BYTES - 73]''')
sub('programs/r1-cost-probe/src/pool_route.rs', '        && (1..=32).contains(&data[1])\n}', '        && 1 <= data[1] && data[1] <= 32\n}')
# K5 aspis-statement (prover-compiled crate)
S = 'crates/aspis-statement/src/'
sub(S + 'pool_v1/pair_forest_semantic_terminal.rs', '''    view[..9]
        .iter()
        .rev()
        .fold(view[9], |acc, bit| acc.add(acc).add(*bit))''', '''    let mut acc = view[9]; let mut i = 9;
    while i > 0 { i -= 1;
        acc = acc.add(acc).add(view[i]); }
    acc''')
sub(S + 'pool_v1/pair_forest_semantic_terminal.rs', '    for index in (0..semantic.len()).rev() {\n',
    '    let mut index = semantic.len(); while index > 0 { index -= 1;\n')
sub(S + 'pool_v1/pair_forest_semantic_terminal.rs', '    for index in (0..poseidon.len()).rev() {\n',
    '    let mut index = poseidon.len(); while index > 0 { index -= 1;\n')
sub(S + 'pool_v1/pair_forest_copy_terminal.rs', '            for index in (0..len).rev() {\n',
    '            let mut index = len; while index > 0 { index -= 1;\n')
sub(S + 'state_only_poseidon.rs', '''    let full_low = [1usize, 9, 10]
        .into_iter()
        .fold(QM31::ZERO, |sum, row| sum.add(selectors.local[row]));
    let internal_low = (2usize..=8).fold(QM31::ZERO, |sum, row| sum.add(selectors.local[row]));''', '''    let full_low = QM31::ZERO
        .add(selectors.local[1]).add(selectors.local[9])
        .add(selectors.local[10]);
    let internal_low = QM31::ZERO.add(selectors.local[2]).add(selectors.local[3]).add(selectors.local[4]).add(selectors.local[5]).add(selectors.local[6]).add(selectors.local[7]).add(selectors.local[8]);''',
    after='pub fn evaluate_state_only_poseidon_oracle_projected(')
# K6 aspis-core (prover-compiled crate)
C = 'crates/aspis-core/src/'
sub(C + 'state_only_hiding.rs', '    for variable in (0..STATE_ONLY_HIDING_SUMCHECK_ROUNDS).rev() {\n',
    '    let mut variable = STATE_ONLY_HIDING_SUMCHECK_ROUNDS; while variable > 0 { variable -= 1;\n')
sub(C + 'state_only_hiding.rs', '    for exponent in (0..STATE_ONLY_HIDING_FACTOR_DEGREE).rev() {\n',
    '    let mut exponent = STATE_ONLY_HIDING_FACTOR_DEGREE; while exponent > 0 { exponent -= 1;\n')
sub(C + 'state_only_prefix.rs', '    for coordinate in (0..z.len()).rev() {\n',
    '    let mut coordinate = z.len(); while coordinate > 0 { coordinate -= 1;\n')
print('ok')
