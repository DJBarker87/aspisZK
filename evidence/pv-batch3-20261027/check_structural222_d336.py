"""Check frozen original/copy controls and their structural call association.
The association is a reviewed structural argument, not native machine proof.
"""
from pathlib import Path
import hashlib,re,json,sys
D=Path(__file__).resolve().parent;R=D.parents[1]
def body(p,n):
 s=(R/p).read_text();a=s.index('{',s.index('fn '+n+'('));i=a+1;depth=1
 while depth:depth+=(s[i]=='{')-(s[i]=='}');i+=1
 return s[a+1:i-1]
def tokens(s):return re.findall(r'\w+|[^\w\s]',re.sub(r'//[^\n]*','',s))
def sha(x):return hashlib.sha256(x).hexdigest()
o='crates/aspis-statement/src/constraints_v4.rs';c='crates/aspis-r1-cost-probe/src/host_multilinear.rs'
bs={p+':'+n:tokens(body(p,n)) for p in [o,c] for n in ['sparse_eq_weights','multilinear_evaluate_qm31']}
pins=D/'structural222-reviewed-tokens.json'
if '--record-reviewed' in sys.argv:pins.write_text(json.dumps(bs,indent=1)+'\n')
assert bs==json.loads(pins.read_text())
original=body(o,'sparse_eq_weights');copy=body(c,'sparse_eq_weights')
# The ordered field expression in the inner traversal is literally equal.
expr='weight = weight.mul(if bit == 0 { QM31::ONE.sub(VALUE) } else { VALUE });'
assert tokens(expr.replace('VALUE','*value'))==tokens(original[original.index('weight = weight.mul'):original.index('});',original.index('weight = weight.mul'))+3])
assert tokens(expr.replace('VALUE','point[coordinate]'))==tokens(copy[copy.index('weight = weight.mul'):copy.index('});',copy.index('weight = weight.mul'))+3])
for text in [original,copy]:assert tokens('let row = (prefix << trailing_boolean) | suffix;')==tokens(text[text.index('let row ='):text.index(';',text.index('let row ='))+1])
# Both folds have exactly the same sum/product order and index expression.
step='sum.add(weight.mul(column[row]))'
assert tokens(step)==tokens(body(o,'multilinear_evaluate_qm31').split('|sum, (row, weight)| {')[1].split('}')[0])
assert tokens('sum = '+step+';')==tokens(body(c,'multilinear_evaluate_qm31').split('let (row, weight) = sparse_weight_at(&weights, i);')[1].split('i +=')[0])
assert 'pub const TRACE_ROWS: usize = 1 << 10;' in (R/'crates/aspis-statement/src/trace_v4.rs').read_text()
out=dict(kind='STRUCTURAL source argument under ruling (k), not machine proof',row='V239',op=222,
 files={p:sha((R/p).read_bytes()) for p in [o,c,'crates/aspis-core/src/field.rs','crates/aspis-statement/src/trace_v4.rs']},
 reviewed_tokens_sha256=sha(pins.read_bytes()),
 ordered_field_calls=['suffix test: raw QM31 ZERO/ONE equality, from the same field.rs','weight: ONE.sub(value) only on zero bit; weight.mul(factor), coordinate ascending','evaluation: weight.mul(column[row]), then sum.add(product), prefix ascending'],
 error_paths='wrong length returns None before sparse construction; same row indices; bounded shifts prefix_len<=10; capacity 2^prefix_len<=1024; no input normalization',
 differences=[dict(change='rev/take_while/count replaced by prefix decrement',lean=['PV_B3_Structural222.scan_value','PV_B3_Structural222.prefix_bound'],argument='same Boolean predicate on the same reversed coordinate sequence; stops before first non-Boolean'),
 dict(change='owned Vec push replaced by indexed fixed storage',lean=['PV_B3_Structural222.take_set_next'],argument='after k writes the populated prefix is exactly k pushed pairs; capacity 2^prefix_len<=1024; remaining initialized cells are never read'),
 dict(change='into_iter fold replaced by index loop',lean=['PV_B3_EvalFold222.source'],argument='same populated prefix consumed once in ascending order; same nested field call order')],
 copy_complete_result='PV_B3_MultilinearFinite222.source',installation='PV_B3_Install222.source',
 native_link_evidence_class='structural argument + extraction',native_differential='receipts/d324-fidelity222-native-01 (finite validation, same length-1024 seven column and zero point)',
 restoration='direct output.data[prefix] write; returned array threaded into next loop; d324 source scan',
 machine_native_equality_claimed=False,XR_imports=False)
(D/'STRUCTURAL222-D336.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
