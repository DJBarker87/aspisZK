"""Pinned, explicit structural normalization of the arithmetic copies.
Only source association: every difference is listed; no native machine theorem.
"""
from pathlib import Path
import json,hashlib,re,sys,subprocess
D=Path(__file__).resolve().parent;R=D.parents[1]
def sha(x):return hashlib.sha256(x).hexdigest()
def tok(s):return re.findall(r'\w+|[^\w\s]',re.sub(r'//[^\n]*','',s))
def body_text(s,n):
 start=s.index('fn '+n+('(' if 'fn '+n+'(' in s else '<'));a=s.index('{',start);i=a+1;depth=1
 while depth:depth+=(s[i]=='{')-(s[i]=='}');i+=1
 return s[a+1:i-1]
def body(p,n,scope=None):
 s=(R/p).read_text()
 if scope:s=s[s.index(scope):]
 return body_text(s,n)
c='crates/aspis-prover/src/host_arithmetic.rs';h='crates/aspis-core/src/state_only_hiding.rs';f='crates/aspis-core/src/field.rs';s='crates/aspis-core/src/state_only_sumcheck.rs'
op=int(sys.argv[1]);assert op in [117,121]
checks=[(c,'state_only_selected_mask_value',None),(h,'state_only_selected_mask_value',None),(h,'selected_mask_linears',None),(c,'selected_mask_linears',None)] if op==117 else [(c,'evaluate_state_only_polynomial',None),(s,'evaluate_state_only_polynomial',None),(f,'qm31_accumulate_product_channels',None),(c,'accumulate_channels',None),(f,'qm31_sum_products_small',None),(c,'qm31_sum_products3',None),(f,'qm31_from_karatsuba_channel_sums',None),(c,'reconstruct_channels',None)]
checks += [(p,n,scope)for p in [c,f]for n in ['new','mul']for scope in ['impl PreparedQm31Multiplier']]
if op==117:checks += [(p,n,None)for p in [c,h]for n in ['cm31_mul_i','cm31_mul_r','mul_tower_basis','mask_power_26']]
pins={p+':'+n:tok(body(p,n,scope))for p,n,scope in checks}
pinfile=D/f'structural{op}-reviewed-tokens.json'
if '--record-reviewed' in sys.argv:pinfile.write_text(json.dumps(pins,indent=1)+'\n')
assert pins==json.loads(pinfile.read_text())
# Noncapturing closures are made explicit; full helper bodies match.
orig_new=body(f,'new','impl PreparedQm31Multiplier');copy_new=body(c,'new','impl PreparedQm31Multiplier')
prep='[component.a, component.b, component.a.add(component.b)]'
assert tok(body(c,'prepare_component'))==tok(prep)
orig_new=orig_new.replace('let prepare = |component: CM31| '+prep+';', '').replace('prepare(', 'prepare_component(')
assert tok(orig_new)==tok(copy_new)
orig_mul=body(f,'mul','impl PreparedQm31Multiplier');copy_mul=body(c,'mul','impl PreparedQm31Multiplier')
a=orig_mul.index('let multiply = |left: [M31; 3], right: CM31| {');b=orig_mul.index('};',a)+2
closure=orig_mul[a:b];inner=closure[closure.index('{')+1:closure.rfind('}')]
assert tok(inner)==tok(body(c,'prepared_component_mul'))
orig_mul=orig_mul[:a]+orig_mul[b:];orig_mul=orig_mul.replace('multiply(', 'prepared_component_mul(').replace('mul_by_r(', 'cm31_mul_r(')
assert tok(orig_mul)==tok(copy_mul)
assert tok(body(f,'mul_by_r'))==tok('CM31 { a: x.a.double().sub(x.b), b: x.a.add(x.b.double()), }')
assert tok(body(c,'cm31_mul_r'))==tok('CM31::new(value.a.double().sub(value.b), value.a.add(value.b.double()))')
assert tok(body(f,'new','impl CM31'))==tok('CM31 { a, b }')
proofs=['PV_B3_PrepareComponent.source','PV_B3_PreparedComponent.source','PV_B3_PreparedNew.source','PV_B3_PreparedMul.source','PV_B3_HostMulR.source']
if op==117:
 for name,value in [('STATE_ONLY_HIDING_C1_COLUMNS',16),('STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS',10),('STATE_ONLY_HIDING_SUMCHECK_ROUNDS',10),('STATE_ONLY_HIDING_FACTOR_DEGREE',26)]:assert f'pub const {name}: usize = {value};' in (R/h).read_text()
 assert tok(body(c,'state_only_selected_mask_value'))==tok('let (linear, explicit_linear) = selected_mask_linears(point); let coefficients = selected_coefficients(c1); let coefficients = mask_only_coefficients(coefficients, mask_only_c1); let shared = selected_horner(coefficients, linear); shared.add(QM31::ONE.add(mask_power_26(explicit_linear)).mul(explicit_g),)')
 for n in ['cm31_mul_i','cm31_mul_r','mul_tower_basis','mask_power_26']:assert tok(body(h,n))==tok(body(c,n))
 old=body(h,'selected_mask_linears');new=body(c,'selected_mask_linears')
 old=old.replace('for variable in (0..STATE_ONLY_HIDING_SUMCHECK_ROUNDS).rev() {','let mut variable = STATE_ONLY_HIDING_SUMCHECK_ROUNDS; while variable > 0 { variable -= 1;')
 assert tok(old)==tok(new)
 for name in ['FACTOR_EXPONENTS','MASK_ONLY_FACTOR_EXPONENTS']:
  def table(p):
   t=(R/p).read_text().split('const '+name+':',1)[1].split('=',1)[1].split(';',1)[0];return tok(t)
  assert table(h)==table(c)
 # Checked original root and each fixed expansion in the existing generator.
 subprocess.run([sys.executable,str(D/'check_range117_source.py')],check=True,stdout=subprocess.DEVNULL)
 proofs+=['PV_B3_Range117.selected','PV_B3_Range117.mask_only','PV_B3_Range117.prepared_horner','PV_B3_LinearsIterator.next_source','PV_B3_LinearsFinite.source','PV_B3_AuditSourceD324.Mask117.source']
 differences=['fixed 16/10 scatters and 26 descending Horner iterations expanded in original order; literal exponent arrays identical','reverse range loop becomes descending index loop; same selected_mask_linears calls','noncapturing prepared closures become explicit helpers; complete-Result transports above']
else:
 # Scalar channel operations retain release wrapping behavior and lexical order.
 old=body(f,'qm31_accumulate_product_channels').replace('left_components','a').replace('right_components','b')
 a=old.index('for component in 0..3 {');tail=old.index('\n    sums',a)
 expanded='\n'.join(f'sums[{i}][{j}] += a[{i}][{j}].0 as u64 * b[{i}][{j}].0 as u64;'for i in range(3)for j in range(3))
 old=old[:a]+expanded+old[tail:]
 assert tok(old)==tok(body(c,'accumulate_channels'))
 old=body(f,'qm31_from_karatsuba_channel_sums');a=old.index('let reconstruct = |channels: [u64; 3]| {');b=old.index('};',a)+2
 closure=old[a:b];inner=closure[closure.index('{')+1:closure.rfind('}')]
 assert tok(inner)==tok(body(c,'reconstruct_component'))
 old=(old[:a]+old[b:]).replace('reconstruct(', 'reconstruct_component(').replace('mul_by_r(', 'cm31_mul_r(')
 assert tok(old)==tok(body(c,'reconstruct_channels'))
 assert tok(body(f,'qm31_sum_products3'))==tok('qm31_sum_products_small(left, right)')
 assert tok(body(f,'qm31_sum_products_small'))==tok('debug_assert!(N >= 2 && N <= 4); let mut sums = [[0u64; 3]; 3]; let mut index = 0usize; while index < N { sums = qm31_accumulate_product_channels(sums, left[index], right[index]); index += 1; } qm31_from_karatsuba_channel_sums(sums)')
 assert tok(body(c,'qm31_sum_products3'))==tok('let sums = accumulate_channels([[0u64; 3]; 3], left[0], right[0]); let sums = accumulate_channels(sums, left[1], right[1]); let sums = accumulate_channels(sums, left[2], right[2]); reconstruct_channels(sums)')
 # The only root change is closure lifting with explicit captured arguments.
 old=body(s,'evaluate_state_only_polynomial');new=body(c,'evaluate_state_only_polynomial')
 a=old.index('let block_value = |block: usize| {');b=old.index('};',a)+2
 closure=old[a:b];inner=closure[closure.index('{')+1:closure.rfind('}')]
 assert tok(inner)==tok(body_text(new,'block_value'))
 a2=new.index('fn block_value(');brace=new.index('{',a2);i=brace+1;depth=1
 while depth:depth+=(new[i]=='{')-(new[i]=='}');i+=1
 new=new[:a2]+new[i:]
 old=old[:a]+old[b:];old=old.replace('block_value(6)','block_value(polynomial, powers, 6)').replace('block_value(block)','block_value(polynomial, powers, block)')
 assert tok(old)==tok(new)
 proofs+=['PV_B3_StructuralArithmetic.three','PV_B3_StructuralArithmetic.append','PV_B3_StructuralArithmetic.lifted_capture','PV_B3_StructuralArithmetic.arity3','PV_B3_AuditSourceD324.Poly121.source_complete']
 differences=['block closure lifted with polynomial and powers explicit; body tokens equal','3x3 channel loops and arity-three aggregation unrolled in unchanged index order; no reassociation','prepared and reconstruction closures lifted; field operations identical','no replacement by naive Horner; raw overflow behavior and grouped product3 retained']
out=dict(kind='STRUCTURAL source argument under ruling (k), not machine proof',op=op,row='V217'if op==117 else 'V220',files={p:sha((R/p).read_bytes())for p in [c,h,f,s]},reviewed_tokens_sha256=sha(pinfile.read_bytes()),exact_helper_normalizations=True,inherited_helper_proof_status='Prepared/field source transports are inherited accepted support; this run checks source token normalization and audits current extraction/installation and generic structural lemmas',differences=differences,lean_transports=proofs,native_link_evidence_class='structural argument + complete-Result extraction',native_differential=('mask117-fidelity-comparison.json'if op==117 else 'polynomial-fidelity-comparison.json')+'; finite same-input validation including raw limbs',canonical_input_assumption_added=False,machine_native_equality_claimed=False,XR_imports=False)
(D/f'STRUCTURAL{op}-D336.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
