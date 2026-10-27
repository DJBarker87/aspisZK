from pathlib import Path
import runpy,sys
P=Path(__file__).resolve().parent; R=P.parents[1]
x=runpy.run_path(str(P/'JGo_arithmetic.py'))
for r in range(2):
 mod=f'JGo_TX2_Round{r}';off=[7527,7783][r]
 imports='\n'.join(f'import JGo_TX2_Cell{r}_{i}\nimport JGo_TX2_Horner{r}_{i}' for i in range(7))
 boundary=x['add'](x['nums'](f'JGo_TX2_Cell{r}_0','value'),x['nums'](f'JGo_TX2_Cell{r}_4','value'))
 claim='JFq_Claim.scalar' if r==0 else 'JGo_TX2_Horner0_6.after'
 s=imports+'\nimport FIo_Install\nimport RowFinish_Control\n'+('import JGo_TX2_Horner0_6\n' if r else '')+f'''set_option autoImplicit false
noncomputable section
namespace AspisR1.{mod}
open Aeneas Aeneas.Std Result AspisR1Stage2.Stage2Finish
attribute [local irreducible] FIn_Polynomial.mul FIn_Primitives.add FIn_Primitives.field
  JFw_Frames.window JFx_NativeBytes.proof

def boundary : E := {x['wide'](boundary)}
theorem boundary_add : FIn_Primitives.add JGo_TX2_Cell{r}_0.value JGo_TX2_Cell{r}_4.value=ok boundary := by
  with_unfolding_all rfl
#print axioms boundary_add

theorem quarter_mul : SAG_StageScale.mulM {claim} 536870912#u32=ok boundary := by
  with_unfolding_all rfl
#print axioms quarter_mul

theorem polynomial : FIn_ExtractInstall.polynomial (JFw_Frames.window {off} 224) JFq_Alpha{r}.scalar=
    ok JGo_TX2_Horner{r}_6.after := by
  rw [FIn_ExtractInstall.same]
  unfold FIn_Polynomial.polynomial
'''
 for step in range(7):
  i=6-step
  s+=f'  rw [FIn_Polynomial.go,JGo_TX2_Horner{r}_{step}.multiply,bind_tc_ok,JGo_TX2_Cell{r}_{i}.source,bind_tc_ok,JGo_TX2_Horner{r}_{step}.addition,bind_tc_ok]\n'
 s+='  rfl\n#print axioms polynomial\n'
 s+=f'''
def values (seed : FinishOps FIo_Install.W) : RowFinish_Control.RoundValues
    (FIo_Install.finishOps (.Ok ()) seed) (JFw_Frames.window {off} 224) JFq_Alpha{r}.scalar {claim} where
  c0 := JGo_TX2_Cell{r}_0.value
  c4 := JGo_TX2_Cell{r}_4.value
  lhs := boundary
  quarter := 536870912#u32
  rhs := boundary
  value := JGo_TX2_Horner{r}_6.after
  field0 := JGo_TX2_Cell{r}_0.source
  field4 := JGo_TX2_Cell{r}_4.source
  add := boundary_add
  quarter_run := rfl
  multiply := quarter_mul
  evaluate := polynomial
#print axioms values
end AspisR1.{mod}
end
'''
 p=R/'lean'/(mod+'.lean')
 if '--check' in sys.argv:assert p.read_text()==s
 else:p.write_text(s)
