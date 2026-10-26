"""Real-byte mask inputs, finite std gathers and canonicality certificates."""
from pathlib import Path
import json,sys
P=Path(__file__).resolve().parent;R=P.parents[1];rows=json.loads((R/'evidence/joint-fixture11-20261026/JFm_WINDOWS.json').read_text())
vals=[[int.from_bytes(bytes(rows[25]['frame'][5+32*i+j:5+32*i+j+4]),'little') for j in range(0,16,4)] for i in range(116)]
alpha=[r['coordinates'] for r in rows[15:25]]
def bound(v):return f'({v[0]}<2147483647 ∧ {v[1]}<2147483647) ∧ ({v[2]}<2147483647 ∧ {v[3]}<2147483647)'
s='''import JFu_Claims
import JFm_PartialAlpha
import FIp_MaskValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFu_MaskInputs
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open FIp_SemanticArithmetic ExtractedMaskCallerModel
open JFu_ClaimsData
'''
s+='def c1 : Array MQ 16#usize := ⟨['+','.join(f'q{i:03}' for i in range(16))+'],by rfl⟩\n'
s+='def maskOnly : Array MQ 10#usize := ⟨['+','.join(f'q{i:03}' for i in range(16,26))+'],by rfl⟩\n'
s+='def g : MQ := q027\ndef point := JFm_PartialAlpha.a10\n'
for name,n,cell,data in [('c1',16,'c1Cell',vals[:16]),('maskOnly',10,'maskCell',vals[16:26])]:
 s+=f'theorem {name}_canonical : ∀ i : Fin {n},CanonicalQM (ExtractedMaskCoefficientStep.{cell} (mapArray {name}) i) := by\n  intro i\n  fin_cases i\n'
 for v in data:s+='  · change '+bound(v)+'\n    omega\n'
 s+=f'#print axioms {name}_canonical\n'
s+='theorem point_canonical : ∀ i : Nat,∀ hi : i<10,CanonicalQM (ExtractedMaskLinearLoop.pointAtNat (mapArray point) i hi) := by\n  intro i hi\n  have cases : '+' ∨ '.join(f'i={j}' for j in range(10))+' := by omega\n  rcases cases with '+'|'.join('h'+str(j) for j in range(10))+'\n'
for v in alpha:s+='  · subst i\n    change '+bound(v)+'\n    omega\n'
s+='#print axioms point_canonical\ntheorem g_canonical : FIp_SemanticValues.Canon g := by\n  change '+bound(vals[27])+'\n  omega\n#print axioms g_canonical\nend AspisR1.JFu_MaskInputs\nend\n'
files={R/'lean/JFu_MaskInputs.lean':s}
s='''import JFu_MaskInputs
import FIp_Install
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFu_MaskGather
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open JFu_ClaimsData JFu_MaskInputs
'''
for n,closure,start,out in [(16,9,0,'c1'),(10,5,16,'maskOnly')]:
 for j in range(n):
  s+=f'''theorem call{n}_{j:02} {{H : Type}} (D : aspis_core.Digest32 H) :
    FinishModel.closureFn{6 if n==16 else 2} D claims {j}#usize=ok (q{start+j:03},claims) := by
'''+('  rfl\n' if n==16 else f'''  have plus : (16#usize+{j}#usize : Result Usize)=ok {16+j}#usize := by
    obtain ⟨v,success,numeric⟩ := WP.spec_imp_exists
      (UScalar.add_spec (x:=16#usize) (y:={j}#usize) (by scalar_tac))
    have same : v={16+j}#usize := by scalar_tac
    exact same ▸ success
  unfold FinishModel.closureFn2
  rw [plus,bind_tc_ok]
  rfl
''')+f'''
#print axioms call{n}_{j:02}
'''
 s+=f'theorem indices{n} : OraclePortStdBuilder.indices {n}#usize=['+','.join(f'{j}#usize' for j in range(n))+'] := rfl\n'+f'#print axioms indices{n}\n'
 s+=f'''theorem gather{n} {{H : Type}} (D : aspis_core.Digest32 H) :
    OraclePortStdBuilder.fromFn {n}#usize (FinishModel.closureFn{closure} D) claims=ok {out} := by
  unfold OraclePortStdBuilder.fromFn
  rw [indices{n}]
  simp only [FinishModel.closureFn9,FinishModel.closureFn5,OraclePortStdBuilder.fromFnLoop,'''+','.join(f'call{n}_{j:02}' for j in range(n))+''',bind_tc_ok,Aeneas.Std.uncurry]
  rfl
'''+f'#print axioms gather{n}\n'
s+='end AspisR1.JFu_MaskGather\nend\n';files[R/'lean/JFu_MaskGather.lean']=s
for f,s in files.items():
 if '--check' in sys.argv:assert f.read_text()==s,f
 else:f.write_text(s)
print('mask preflight:',len(files),'files;26 gather calls;37 canonical cells, no large normalization')
