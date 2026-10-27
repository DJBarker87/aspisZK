"""One combined closing-theorem axioms audit followed by a focused closure check."""
from pathlib import Path
import re,json,hashlib,sys
D=Path(__file__).resolve().parent;L=D/'lean'
roots=['PV_B3_MultilinearFinite222','PV_B3_EvalFold222','PV_B3_MaskDictionary134','PV_B3_AuditSourceD324']
seen=set();order=[]
def visit(m):
 if m in seen or not m.startswith('PV_B3_'):return
 seen.add(m);p=L/(m+'.lean');assert p.exists(),m
 for imp in re.findall(r'^import\s+(\S+)',p.read_text(),re.M):visit(imp)
 order.append(m)
for m in roots:visit(m)
names=[]
for m in order:
 ns=''
 for line in (L/(m+'.lean')).read_text().splitlines():
  n=re.match(r'^namespace\s+(\S+)',line)
  if n:ns=n[1];continue
  if line.startswith('end '):ns='';continue
  n=re.match(r'^\s*(?:noncomputable\s+)?theorem\s+([\w.]+)',line)
  if n and ns:names.append(ns+'.'+n[1])
head=''.join('import '+m+'\n' for m in roots)
head+='\n-- Combined audit: every theorem in the private closing-source cone.\n'
head+=''.join('#print axioms '+n+'\n' for n in dict.fromkeys(names))
body='''
namespace PV_B3_ClosureD324
open Aeneas Aeneas.Std Result
set_option autoImplicit false
abbrev Q222 := PV_B3_Copy_222.aspis_core.field.QM31
abbrev Q117 := PV_B3_Copy_117.aspis_core.field.QM31

-- This packet states the precise checked copy/control/carrier facts. Native
-- original/copy laws, row adoption and the privacy endpoint remain separate.
theorem closure :
    (∀ (column : Slice Q222) (point : Array Q222 10#usize),
      PV_B3_Copy_222.host_multilinear.multilinear_evaluate_qm31 column point =
        PV_B3_MultilinearFinite222.evaluate column point) ∧
    (∀ (column : Slice Q222) (weights : PV_B3_Copy_222.host_multilinear.SparseWeights)
        (sum : Q222) (i : Usize), i.val ≤ weights.len.val → weights.len.val ≤ 1024 →
      PV_B3_Copy_222.host_multilinear.multilinear_evaluate_qm31_loop column weights sum i =
        PV_B3_EvalFold222.fold column
          ((weights.data.val.drop i.val).take (weights.len.val-i.val)) sum) ∧
    (PV_B3_MaskDictionary134.translate
        PV_B3_Forest_134.host_forest.pool_v1_pair_forest_copy_active_row_masks_v1 =
      PV_CBM_ReferenceRaw.reference.masks) ∧
    (∀ (base : ProverRwFull.ExternalTypes)
        (ops : @ProverRwFull.ExternalFuns (R1Z.PV_CBM_MasksSelection.Types base)),
      PV_B3_MaskDictionary134.selected base ops = R1Z.PV_CBM_MasksSelection.selected base ops) ∧
    (∀ (r : Result PV_B3_MaskDictionary134.NewFinal),
      PV_B3_AuditSourceD324.Errors134.restore (PV_B3_MaskDictionary134.translate r) = r) ∧
    (∀ (c1 : Array Q117 16#usize) (mask : Array Q117 10#usize)
        (g : Q117) (point : Array Q117 10#usize),
      PV_B3_Copy_117.host_arithmetic.state_only_selected_mask_value c1 mask g point =
        PV_B3_AuditSourceD324.Mask117.reference c1 mask g point) ∧
    (∀ (poly : Array Q117 28#usize) (x : Q117),
      PV_B3_Copy_117.host_arithmetic.evaluate_state_only_polynomial poly x =
        PV_B3_AuditSourceD324.Poly121.reference poly x) ∧
    (∃ m : Array U16 64#usize,
      PV_B3_MaskDictionary134.translate
          PV_B3_Forest_134.host_forest.pool_v1_pair_forest_copy_active_row_masks_v1 =
        ok (.Ok m) ∧ m.val.length = 64) := by
  exact ⟨PV_B3_MultilinearFinite222.source, PV_B3_EvalFold222.source,
    PV_B3_MaskDictionary134.copy_reference, PV_B3_MaskDictionary134.dictionary,
    PV_B3_AuditSourceD324.Errors134.roundtrip, PV_B3_AuditSourceD324.Mask117.source,
    PV_B3_AuditSourceD324.Poly121.source_complete, PV_B3_MaskDictionary134.nonvacuity⟩

#print closure
#print axioms closure
end PV_B3_ClosureD324
'''
s=head+body;p=L/'PV_B3_ClosureD324.lean'
if '--check' in sys.argv:assert p.read_text()==s
else:p.write_text(s)
meta={'roots':roots,'private_cone':order,'audit_declarations':list(dict.fromkeys(names)),
 'closing_source_sha256':hashlib.sha256(s.encode()).hexdigest(),
 'layout':'axiom audit first; focused closure theorem then checked and printed in the same final target',
 'project_extra_imports':'seven privately compiled h5 R1Z modules recorded in d324-op134-dictionary-resolution.json'}
if '--check' not in sys.argv:(D/'d324-closure-manifest.json').write_text(json.dumps(meta,indent=2)+'\n')
print(json.dumps({'private_modules':len(order),'axiom_reports':len(set(names)),'source_sha256':meta['closing_source_sha256']}))
