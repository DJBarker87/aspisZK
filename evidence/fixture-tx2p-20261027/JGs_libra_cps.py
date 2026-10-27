from pathlib import Path
import sys
R=Path(__file__).resolve().parents[2];src=(R/'lean/FJm_LibraStages.lean').read_text();out={}
items=[('Powers','powers','extra side','(extra : Array NQ 2#usize) (side : Usize)','(base high : Array NQ 4#usize) (q4 q16 : NQ)','Array NQ 4#usize → Array NQ 4#usize → NQ → NQ → Result R','base high q4 q16'),('Term','term','ap1 high j','(ap1 : Weights) (high : Array NQ 4#usize) (j : Usize)','(i : Usize) (t : NE)','Usize → NE → Result R','i t'),('Totals','totals','terms','(terms : Weights)','(first2 first3 all : NE)','NE → NE → NE → Result R','first2 first3 all')]
for title,fn,args,params,unused,ktype,knames in items:
 ns='JGs_Libra'+title+'Bind';a=src.index('def '+fn+' ');a=src.index(':= do',a)+len(':= do');b=src.index('\n\ndef ',a);body=src[a:b]
 if fn=='powers':body=body.replace('  ok (Array.make 4#usize [aspis_core.field.QM31.ONE,q1,q2,q3],\n    Array.make 4#usize [aspis_core.field.QM31.ONE,q41,q8,q12],q41,q16)','  K (Array.make 4#usize [aspis_core.field.QM31.ONE,q1,q2,q3])\n    (Array.make 4#usize [aspis_core.field.QM31.ONE,q41,q8,q12]) q41 q16');pattern='(base,high,q4,q16)'
 elif fn=='term':body=body.replace('  ok (i,term)','  K i term');pattern='(i,t)'
 else:body=body.replace('  ok (first2,first3,all)','  K first2 first3 all');pattern='(first2,first3,all)'
 s=f'''import FJm_LibraStages
set_option autoImplicit false
noncomputable section
namespace AspisR1.{ns}
open Aeneas Aeneas.Std Result ControlFlow FIo_Native
open FIo_FieldBridge (NE NQ)
open FJm_LibraStages (Weights)
def thenCall {{R : Type}} {params} (K : {ktype}) : Result R := do'''+body+f'''
/-- A single symbolic chunk, with its remaining continuation opaque. -/
theorem source {{R : Type}} {params} (K : {ktype}) :
    thenCall {args} K=(do let {pattern} ← FJm_LibraStages.{fn} {args}; K {knames}) := by
  unfold thenCall FJm_LibraStages.{fn}
  simp only [bind_assoc_eq,bind_tc_ok,Aeneas.Std.uncurry] <;> with_unfolding_all rfl
#print axioms source
end AspisR1.{ns}
end
''';out[ns]=s
for mod,s in out.items():
 p=R/'lean'/(mod+'.lean')
 if '--check' in sys.argv:assert (p if p.exists() else R/'evidence/fixture-tx2p-20261027/JGs_UNCHECKED'/(p.name+'.txt')).read_text()==s,mod
 else:p.write_text(s)
print(len(out),'opaque-continuation Libra chunks')
