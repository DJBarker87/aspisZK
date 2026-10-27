"""Promote exact mutable-output row extraction, with explicit complete-Result wrapper."""
from pathlib import Path
import re,json,hashlib,sys
root=Path(__file__).resolve().parents[2];ev=root/'evidence/pv-cbmid-20261027';base=root/'docs/research/v8-r0-zk-20261009/lean/R1Z'
source=ev/'aeneas-op133fill-001/Funs.lean';text=source.read_text();types=(source.parent/'Types.lean').read_text()
assert 'PV_CBM_Op133fillRaw' in text
assert re.search(r'inductive aspis_statement\.pool_v1\.pair_tree_hiding\.PoolV1PairHidingLayoutErrorV1',types)
start=text.index('/-- [pv_cbm_source::reference::fill_rows]');end=text.index('\nend PV_CBM_Op133fillRaw',start)
section=text[start:end].replace('PV_CBM_Op133fillRaw','PV_CBM_RowsRaw')
assert section.count('def reference.fill_rows')==1
outputs={}
outputs['PV_CBM_RowsReference']='''import R1Z.PV_CBM_ReferenceTypes
open Aeneas Aeneas.Std Result ControlFlow Error
namespace PV_CBM_RowsRaw
abbrev aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairHidingLayoutErrorV1 :=
  PV_CBM_ReferenceRaw.aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairHidingLayoutErrorV1
'''+section+'''
#print axioms reference.fill_rows
end PV_CBM_RowsRaw
'''
outputs['PV_CBM_RowsSelection']='''import R1Z.PV_CBM_RowsReference
import R1Z.PV_CBM_CellsSelection
namespace R1Z.PV_CBM_RowsSelection
open Aeneas Aeneas.Std Result ProverRwFull
set_option autoImplicit false
noncomputable section
abbrev Types := PV_CBM_CellsSelection.Types

def callback : Result (core.result.Result (alloc.vec.Vec U16) PV_CBM_CellsMaterializer.LayoutError) :=
  PV_CBM_CellsMaterializer.snapshot (PV_CBM_RowsRaw.reference.fill_rows (alloc.vec.Vec.new U16))

@[reducible] def selected (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns (Types base) :=
  letI : ExternalTypes := Types base
  {PV_CBM_CellsSelection.selected base ops with op133 := callback}

/-- Reference-only: no native shipped/reference equality is asserted. -/
theorem op133_reference (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op133 (Types base) (selected base ops) = callback := rfl
#print axioms op133_reference
end
end R1Z.PV_CBM_RowsSelection
'''
check='--check' in sys.argv
for name,s in outputs.items():
 p=base/(name+'.lean')
 if check:assert p.read_text()==s
 else:p.write_text(s)
record=dict(input_Funs_sha256=hashlib.sha256(text.encode()).hexdigest(),input_Types_sha256=hashlib.sha256(types.encode()).hexdigest(),normalization='Namespace/import replacement; same frozen Rust layout-error carrier alias; generic complete-Result fresh-vector wrapper retained explicitly.',status='Reference selection only; native association unproved',outputs={n:hashlib.sha256(s.encode()).hexdigest() for n,s in outputs.items()})
if check:assert json.loads((ev/'ROWS-CERTIFICATE.json').read_text())==record
else:(ev/'ROWS-CERTIFICATE.json').write_text(json.dumps(record,indent=2)+'\n')
print('CHECK' if check else 'GENERATED',len(outputs),'modules')
