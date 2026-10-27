from pathlib import Path
R=Path.cwd();P=R/'crates/aspis-prover';D=R/'crates/aspis-r1-cost-probe/src'
h=(R/'crates/aspis-core/src/state_only_hiding.rs').read_text();s=(R/'crates/aspis-core/src/state_only_sumcheck.rs').read_text()
def section(t,a,b):return t[t.index(a):t.index(b,t.index(a))]
text='''//! Prover-local selected mask/polynomial arithmetic. Field operation order
//! is copied literally; no Horner regrouping or raw-limb normalization occurs.
use aspis_core::field::{CM31,M31,QM31,PreparedQm31Multiplier,qm31_sum_products3};
use aspis_core::state_only_hiding::{STATE_ONLY_HIDING_C1_COLUMNS,STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS,STATE_ONLY_HIDING_SUMCHECK_ROUNDS,STATE_ONLY_HIDING_FACTOR_DEGREE};
use aspis_core::state_only_sumcheck::StateOnlySumcheckPolynomial;
'''
text+=section(h,'const FACTOR_EXPONENTS:', 'const EXPLICIT_FACTOR_EXPONENT:')
text+=section(h,'#[inline(always)]\nfn cm31_mul_i(', '/// Cache the shared dense')
linears=section(h,'#[inline(always)]\nfn selected_mask_linears(', '\nfn mask_power(').replace('for variable in (0..STATE_ONLY_HIDING_SUMCHECK_ROUNDS).rev() {','let mut variable=STATE_ONLY_HIDING_SUMCHECK_ROUNDS;while variable>0{variable-=1;')
text+=linears+section(h,'#[inline(always)]\nfn mask_power_26(', '\nfn explicit_mask_factor(')
body=section(h,'#[inline(never)]\npub fn state_only_selected_mask_value(', '\n/// Bind the final semantic mask-cell')
body=body.replace('for column in 0..STATE_ONLY_HIDING_C1_COLUMNS {','let mut column=0usize;while column<STATE_ONLY_HIDING_C1_COLUMNS {').replace('for column in 0..STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS {','let mut column=0usize;while column<STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS {').replace('mul_tower_basis(c1[column], column & 3);','mul_tower_basis(c1[column], column & 3);column+=1;').replace('mul_tower_basis(mask_only_c1[column], column & 3);','mul_tower_basis(mask_only_c1[column], column & 3);column+=1;').replace('for exponent in (0..STATE_ONLY_HIDING_FACTOR_DEGREE).rev() {','let mut exponent=STATE_ONLY_HIDING_FACTOR_DEGREE;while exponent>0{exponent-=1;')
text+=body
body=section(s,'#[inline(never)]\npub fn evaluate_state_only_polynomial(', '\n#[cfg(')
a=body.index('    let block_value =');b=body.index('    let mut accumulator',a)
body=body[:a]+'''    fn block_value(polynomial:&StateOnlySumcheckPolynomial,powers:[QM31;3],block:usize)->QM31{
        let start=4*block;polynomial[start].add(qm31_sum_products3(powers,[polynomial[start+1],polynomial[start+2],polynomial[start+3]]))
    }
'''+body[b:];body=body.replace('block_value(6)','block_value(polynomial,powers,6)').replace('block_value(block)','block_value(polynomial,powers,block)');text+=body
(P/'src/host_arithmetic.rs').write_text(text)
p=P/'src/lib.rs';p.write_text(p.read_text()+'\n#[cfg(feature="prover")]\npub mod host_arithmetic;\n')
# Host caller imports select the copy only under the explicit prover gate.
for file,name,original in [('state_only_hiding.rs','state_only_selected_mask_value','aspis_core::state_only_hiding'),('state_only_zerocheck.rs','evaluate_state_only_polynomial','aspis_core::state_only_sumcheck')]:
 p=P/'src'/file;t=p.read_text();i=t.index('use '+original+'::{');j=t.index('};',i)+2;t=t[:i]+t[i:j].replace(name+',','')+t[j:];i=t.index('\nconst ') if '\nconst 'in t else t.index('\n#[derive');t=t[:i]+f'\n#[cfg(feature="prover")]\nuse crate::host_arithmetic::{name};\n#[cfg(not(feature="prover"))]\nuse {original}::{name};\n'+t[i:];p.write_text(t)
p=D/'host_semantic.rs';t=p.read_text().replace('aspis_core::state_only_hiding::state_only_selected_mask_value','aspis_prover::host_arithmetic::state_only_selected_mask_value');p.write_text(t)
p=D/'host_terminal.rs';t=p.read_text().replace('state_only_hiding::{state_only_selected_mask_value, STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS}', 'state_only_hiding::STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS');t=t.replace('use crate::host_copy_terminal::','use aspis_prover::host_arithmetic::state_only_selected_mask_value;\nuse crate::host_copy_terminal::',1);p.write_text(t)
p=D/'host_sumcheck.rs';t=p.read_text().replace('evaluate_state_only_polynomial, state_only_boundary_sum,','state_only_boundary_sum,');t=t.replace('    use aspis_core::state_only_sumcheck::{','    use aspis_prover::host_arithmetic::evaluate_state_only_polynomial;\n    use aspis_core::state_only_sumcheck::{',1);p.write_text(t)
