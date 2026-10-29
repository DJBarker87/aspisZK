"""Instantiate all nine source accumulation stores with named matrix laws.
This does not assert the accumulator's complete native differential or row law.
"""
from pathlib import Path
import json,sys,re,hashlib
D=Path('evidence/pv-b3p6-20261028');L=D/'lean';P=Path('tools/pv-b3p6-20261028/v244');raw=(P/'reference_field.rs').read_text();a=raw.index('fn accumulate_prepared227(');b=raw.index('pub(crate) fn qm31_sum_products3_prepared',a);body=raw[a:b]
pattern=r'sums\[(\d)\]\[(\d)\]\+=left\.components\[\1\]\[\2\]\.0 as u64 \* right_components\[\1\]\[\2\]\.0 as u64;'
stores=re.findall(pattern,body);assert stores==[(str(c),str(k))for c in range(3)for k in range(3)],stores
rows=[]
for c,k in stores:
 module=f'PV_B3P_MatrixCell9{c}{k}227';law=f'accumulation_store9_{c}_{k}'
 code=f'''import PV_B3P_MatrixCell9227
namespace PV_B3P_Binding9227
open Aeneas Aeneas.Std
set_option autoImplicit false

theorem {law} (sums : Matrix3x3) (left right : U32) :
    matrix_cell sums {c}#usize {k}#usize left right =
      .ok (matrix_put sums {c}#usize {k}#usize (by change {c}<3; omega) (by change {k}<3; omega) left right) :=
  matrix_cell_result sums {c}#usize {k}#usize (by change {c}<3; omega) (by change {k}<3; omega) left right
#print axioms {law}
end PV_B3P_Binding9227
'''
 p=L/(module+'.lean')
 if '--check'in sys.argv:assert p.read_text()==code
 else:p.write_text(code)
 rows.append(dict(module=module,component=int(c),channel=int(k),theorem=law,source_statement=f'sums[{c}][{k}]+=left.components[{c}][{k}].0 as u64 * right_components[{c}][{k}].0 as u64;',credit='single source-store model law; application to complete emitted accumulator body still required'))
x=dict(rows=rows,owned_body_sha256=hashlib.sha256(body.encode()).hexdigest(),all_nine_owned_stores_enumerated=True,whole_body_bound=False,D188_native_comparison=False,direct_native_matrix_comparison=False)
p=D/'resume9/matrix-store-bindings.json'
if '--check'in sys.argv:assert json.loads(p.read_text())==x
else:p.write_text(json.dumps(x,indent=2)+'\n')
print(json.dumps(dict(modules=[r['module']for r in rows],source_stores=len(rows))))
