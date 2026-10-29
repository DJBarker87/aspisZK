from pathlib import Path
import re,json,hashlib
D=Path('evidence/pv-b3q-20261029');L=D/'lean'
excluded={'PV_B3Q_FormatCounterexample','PV_B3Q_Combined','PV_B3Q_Axioms','PV_B3Q_Manifest'}
proofs=[];theorems=[]
for p in sorted(L.glob('PV_B3Q_*.lean')):
 if p.stem in excluded:continue
 names=re.findall(r'^theorem\s+([A-Za-z0-9_]+)',p.read_text(),re.M)
 if not names:continue
 namespace=re.search(r'^namespace\s+(\S+)',p.read_text(),re.M)[1]
 proofs.append(p.stem);theorems.extend(namespace+'.'+name for name in names)
combined=''.join('import '+m+'\n'for m in proofs)+'''namespace PV_B3Q_Combined
open Aeneas Aeneas.Std PV_B3P_Groups14227 PV_B3P_Binding14227
set_option autoImplicit false
/-- Joint non-vacuity for these explicit, partial source ports. This is not a
complete deployed catalogue or a new callback/endpoint decomposition. -/
theorem joint_scope_witness :
    ∃ (store : Store14)
      (matrixStore : Matrix14 → Usize → Usize → U64 → Result Matrix14)
      (slice : SliceFn14),
      PV_B3P_Link_D188 store ∧ PV_B3P_Link_matrix_stores matrixStore ∧
      PV_B3P_Link_slice14 slice ∧
      PV_B3P_Link_std_dependency_closure14 (PV_B3Q_Std.Signature Unit Unit)
        (PV_B3Q_Std.native Unit Unit) (PV_B3Q_Std.model Unit Unit) :=
 ⟨PV_B3Q_D188.direct_store,PV_B3Q_Matrix.deployed_store,PV_B3Q_FourSlice.source,
   PV_B3Q_D188.direct_store_link,PV_B3Q_Matrix.deployed_store_link,
   PV_B3Q_FourSlice.source_link,PV_B3Q_Std.partial_catalogue_link Unit Unit⟩
#print axioms joint_scope_witness
end PV_B3Q_Combined
'''
(L/'PV_B3Q_Combined.lean').write_text(combined);theorems.append('PV_B3Q_Combined.joint_scope_witness')
(L/'PV_B3Q_Axioms.lean').write_text('import PV_B3Q_Combined\n'+''.join('#print axioms '+n+'\n'for n in theorems))
fixtures=sorted(p.stem for p in L.glob('PV_B3Q_*Fixture*.lean'))
manifest='import PV_B3Q_Axioms\n'+''.join('import '+m+'\n'for m in fixtures)+'#check PV_B3Q_Combined.joint_scope_witness\n#print axioms PV_B3Q_Combined.joint_scope_witness\n'
(L/'PV_B3Q_Manifest.lean').write_text(manifest)
source_rows=[dict(module=m,path=str(L/(m+'.lean')),sha256=hashlib.sha256((L/(m+'.lean')).read_bytes()).hexdigest())for m in proofs+fixtures+['PV_B3Q_Combined','PV_B3Q_Axioms','PV_B3Q_Manifest']]
out=dict(proof_modules=proofs,fixture_modules=fixtures,theorems=theorems,sources=source_rows,excluded_quarantined=['PV_B3Q_FormatCounterexample'],audit_ids=[70297,70298,70299],complete_deployed_catalogue=False)
(D/'frozen-manifest.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(dict(proof_modules=len(proofs),fixture_modules=len(fixtures),theorems=len(theorems))))
