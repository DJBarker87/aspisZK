"""Copy exact selected Rust function spans into an extraction-only crate context."""
from pathlib import Path
import hashlib,json
root=Path(__file__).resolve().parents[2];out=root/'tools/pv-cbmid-20261027';pins=[]
def function(path,name):
 text=(root/path).read_text();pos=text.index('fn '+name+'(')
 start=text.rfind('\n',0,pos)+1
 if text[start:pos].strip() not in ('','pub'):raise ValueError(text[start:pos])
 brace=text.index('{',pos);depth=1;end=brace+1
 while depth:
  if text[end]=='{':depth+=1
  if text[end]=='}':depth-=1
  end+=1
 code=text[start:end]
 pins.append(dict(path=path,name=name,line_start=text[:start].count('\n')+1,line_end=text[:end].count('\n')+1,source_sha256=hashlib.sha256(text.encode()).hexdigest(),function_sha256=hashlib.sha256(code.encode()).hexdigest()))
 return code
p='crates/aspis-statement/src/constraints_v4.rs'
s='use alloc::vec::Vec;\nuse aspis_core::field::QM31;\nuse aspis_statement::trace_v4::TRACE_ROWS;\n'
for f in ['eq_row','sparse_eq_weights','multilinear_evaluate_qm31']:s+=function(p,f)+'\n'
(out/'constraints-fragments.rs').write_text(s)
p='crates/aspis-statement/src/pool_v1/pair_forest_semantic_oracle.rs'
s='use alloc::vec::Vec;\nuse aspis_core::field::QM31;\nuse aspis_statement::logup::build_copy_logup_helper;\nuse aspis_statement::pool_v1::pair_trace::PoolV1PairTraceErrorV1;\nuse aspis_statement::pool_v1::pair_forest_trace::{PoolV1PairForestTraceV1,pool_v1_pair_forest_copy_rows_v1};\n'
s+=function(p,'build_pool_v1_pair_forest_copy_helper_v1')+'\n'
(out/'oracle-fragments.rs').write_text(s)
(root/'evidence/pv-cbmid-20261027/FRAGMENT-PINS.json').write_text(json.dumps(dict(scope='Exact copied function spans; dependencies remain unedited. This is input provenance, not a complete extraction theorem.',functions=pins),indent=2)+'\n')
