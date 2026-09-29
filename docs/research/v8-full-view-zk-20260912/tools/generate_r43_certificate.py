#!/usr/bin/env python3
"""Emit a small fixed-matrix certificate; never unfold a query-root recurrence."""
import argparse,hashlib,json
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--input',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--check',action='store_true');a=p.parse_args();d=json.loads(a.input.read_text())
assert d['selected_kernel_columns']==list(range(6,18))+[29]
assert d['z']==[0,0,0,1,1,0,0,1,0,2] and d['determinant']==2079196465
assert len(d['matrix'])==len(d['inverse'])==13 and all(len(r)==13 for r in d['matrix']+d['inverse'])
header='/- Generated fixed high-coordinate certificate. No query recurrence is evaluated. -/\n'
ns='namespace AspisR19.HighWitnessData\nopen RootCertificate\nnoncomputable section\n';end='end\nend AspisR19.HighWitnessData\n';files={}
data=header+'import AspisV8R19.SparseHighWitness\nimport AspisV8R19.ResidualNonsingular\n'+ns
for name,values in [('expectedMatrix',d['matrix']),('inverseMatrix',d['inverse'])]:
    data+=f'def {name} : Matrix (Fin 13) (Fin 13) M := fun i j =>\n  (({values!r} : List (List Nat)).getD i.val []).getD j.val 0\n'
files['HighWitnessData.lean']=data+end
files['HighWitnessEntries.lean']=header+'import AspisV8R19.HighWitnessData\n'+ns+'''theorem model_matrix : SparseHighWitness.matrix = expectedMatrix := by
  funext i j
  fin_cases i <;> fin_cases j <;> decide
#print axioms model_matrix
'''+end
finish=header+'import AspisV8R19.HighWitnessEntries\n'
for i in range(13):
    name=f'HighWitnessInverseRow{i:02}.lean'
    files[name]=header+'import AspisV8R19.HighWitnessData\n'+ns+f'''theorem inverse_row{i} (j : Fin 13) : (expectedMatrix*inverseMatrix) {i} j = (1:Matrix (Fin 13) (Fin 13) M) {i} j := by
  fin_cases j <;> (rw [Matrix.mul_apply]; decide)
#print axioms inverse_row{i}
'''+end
    finish+=f'import AspisV8R19.HighWitnessInverseRow{i:02}\n'
finish+=ns+'''theorem right_inverse : expectedMatrix*inverseMatrix=1 := by
  funext i j
  fin_cases i
'''
for i in range(13):finish+=f'  · exact inverse_row{i} j\n'
finish+='''theorem expected_det_ne_zero : expectedMatrix.det ≠ 0 := by
  letI : Nontrivial M := ⟨⟨0,1,by decide⟩⟩
  exact ResidualNonsingular.right_inverse_det_ne_zero _ _ right_inverse
theorem model_det_ne_zero : SparseHighWitness.matrix.det ≠ 0 := by
  rw [model_matrix]
  exact expected_det_ne_zero
#print axioms right_inverse
#print axioms expected_det_ne_zero
#print axioms model_det_ne_zero
'''+end
files['HighWitnessNonzero.lean']=finish
if not a.check:a.output.mkdir(parents=True,exist_ok=True)
for n,s in files.items():
    dest=a.output/n
    if a.check:assert dest.read_text()==s,n
    else:assert not dest.exists();dest.write_text(s)
print(json.dumps({'mode':'check'if a.check else'write','files':len(files),'declarations':17,'input_sha256':hashlib.sha256(a.input.read_bytes()).hexdigest(),'source_bound_matrix':True,'universal_root_theorem':False}))
