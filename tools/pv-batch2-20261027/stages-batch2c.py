"""Exact source suffixes at the fixed factor-row boundaries, no constructor evaluation."""
from pathlib import Path
import sys,re
L=Path('docs/research/v8-r0-zk-20261009/lean/R1Z');outs={}
params='(variant : transport.Variant) (points : Points) (extra : Array K 2#usize) (z : Array Point 2#usize) (factors : Factors)'
for i in reversed(range(5)):
 s=(L/f'PV_B2_C_ConstructorRow{i}.lean').read_text();body=s.split(' : Result Factors := do\n',1)[1].split(f'\ntheorem row{i}_total',1)[0];a=body.rindex('  ok (');out=body[a+len('  ok '):].strip();body=body[:a]
 final='(ok (core.result.Result.Ok ({variant,factors := factors,points,extra} : host_weights.Weights)) : Result (core.result.Result host_weights.Weights verifier.Error))'
 nxt=f'stage{i+1} variant points extra z factors' if i<4 else final
 call=f'stage{i+1} variant points extra z {out}' if i<4 else final.replace('factors := factors', 'factors := '+out)
 body+='  '+call+'\n';v='points' if i<3 else 'z'
 imp='PV_B2_C_Row4Cps' if i==4 else f'PV_B2_C_ConstructorStage{i+1}'
 proof=(L/f'PV_B2_C_Row{i}Cps.lean').read_text().split(') := by\n',1)[1].split(f'#print axioms row{i}_cps',1)[0]
 proof='  symm\n  unfold stage'+str(i)+'\n'+re.sub(r'\bk\b','(fun (factors : Factors) => '+nxt+')',proof)
 text=f'''import R1Z.{imp}
set_option autoImplicit false
namespace PV_B2_C_ConstructorStages
open Aeneas Aeneas.Std Result PV_B2_C_ArrayTotal
open PV_B2_C_WeightsNative PV_B2_C_ConstructorRows
/-- Exact source suffix cut at factor row {i}. -/
def stage{i} {params} : Result (core.result.Result host_weights.Weights verifier.Error) := do
'''+body+f'''
theorem stage{i}_eq {params} :
    stage{i} variant points extra z factors =
      (row{i} factors {v} >>= fun (factors : Factors) => {nxt}) := by
{proof}

theorem stage{i}_total {params} : RustOk (stage{i} variant points extra z factors) := by
  rw [stage{i}_eq]
  apply bind_rust _ _ (row{i}_total factors {v})
  intro factors
'''+('  exact ⟨_,rfl⟩' if i==4 else f'  exact stage{i+1}_total variant points extra z factors')+f'''
#print axioms stage{i}_eq
#print axioms stage{i}_total
end PV_B2_C_ConstructorStages
'''
 outs[L/f'PV_B2_C_ConstructorStage{i}.lean']=text
for p,s in outs.items():
 if '--check' in sys.argv:assert p.read_text()==s
 else:p.write_text(s)
