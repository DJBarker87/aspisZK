from pathlib import Path
import sys
R=Path(__file__).resolve().parents[2]
x={'__file__':str(R/'evidence/fixture-tx2n-20261027/JGo_arithmetic.py')};exec((R/'evidence/fixture-tx2n-20261027/JGo_arithmetic.py').read_text().split('mods,results=generate()')[0],x)
out={}
for k,kind,previous in [(1,2,None),(3,5,1),(4,6,3)]:
 ns=f'JGs_K{k}';s0=x['nums'](f'JGs_S{k}0','value');s1=x['nums'](f'JGs_S{k}1','value');scale=x['mul'](s0,s1);value=x['mul'](scale,x['nums'](f'JGs_D{k}Data','value'))
 imports=['FJr_KindIndices','JGs_KindForward',f'JGs_T{k}',f'JGs_S{k}0',f'JGs_S{k}1',f'JGs_D{k}']
 if previous:imports+=[f'JGs_K{previous}']
 before='JGq_PairPrefix.initial' if previous is None else f'JGs_K{previous}.parts'
 scratch='JGq_PairShape.scratch' if previous is None else f'JGs_K{previous}.scratch'
 if previous is None:imports+=['JGq_PairPrefix']
 s='\n'.join('import '+m for m in imports)+f'''
set_option autoImplicit false
noncomputable section
namespace AspisR1.{ns}
open Aeneas Aeneas.Std Result
abbrev E := FIo_Install.NE
abbrev Q := FIo_Install.NQ
def scale : E := {x['wide'](scale)}
def value : E := {x['wide'](value)}
def scratch : alloc.vec.Vec Q := ⟨JGs_T{k}.s21.val,JGs_T{k}.s21.property⟩
def parts : Array E 7#usize := ({before}).set {kind}#usize value
theorem multiply : FIo_Native.aspis_core.field.wide_exact.WideExact.mul JGs_S{k}0.value JGs_S{k}1.value=ok scale := by with_unfolding_all rfl
#print axioms multiply
theorem scaled : FIo_Native.aspis_core.field.wide_exact.WideExact.mul scale JGs_D{k}.value=ok value := by with_unfolding_all rfl
#print axioms scaled
/-- This real-byte kind consumes the preceding kind's native scratch and write. -/
theorem source : @FIo_Native.weights.process_kind (FIo_Install.allocation (.Ok ()))
    JGq_PairShape.w {kind}#usize JGq_PairShape.alpha JGq_PairShape.f 2#usize 64#usize
    JGq_Powers0.a4 JGq_Powers1.a4 {scratch} {before}=ok (.Ok (),scratch,parts) := by
  letI := FIo_Install.allocation (.Ok ())
  have row : Array.index_usize JGq_PairShape.w.factors {k}#usize=
      ok (FIn_WeightsInstall.mapArray (FIn_WeightsInstall.mapArray FIo_Install.toQ) JGo_TX2_WeightData.r{k}_5) := by rfl
  have borrow : alloc.vec.Vec.deref_mut {scratch}=
      (JGs_T{k}.input,fun t : Slice Q=> (⟨t.val,t.property⟩ : alloc.vec.Vec Q)) := by with_unfolding_all rfl
  have write : Array.update {before} {kind}#usize value=ok parts := by
    obtain ⟨a,ha,eq⟩ := WP.spec_imp_exists (Array.update_spec {before} {kind}#usize value (by scalar_tac))
    subst a
    exact ha
  exact JGs_KindForward.source JGq_PairShape.w (by rfl) {kind}#usize {k}#usize
    (by simp only [show {'' if kind==2 else '¬'}({kind}#usize<4#usize) from by decide,{'ite_true' if kind==2 else 'ite_false'}]; apply UScalar.eq_of_val_eq; rw [FJr_KindIndices.sub _ _ (by decide) (by decide)];rfl) JGq_PairShape.alpha JGq_PairShape.f 64#usize JGq_Powers0.a4 JGq_Powers1.a4
    {scratch} JGs_T{k}.input JGs_T{k}.s21 (fun t=>⟨t.val,t.property⟩) borrow
    _ JGs_S{k}0.row JGs_S{k}1.row JGs_S{k}0.value JGs_S{k}1.value scale JGs_D{k}.value value
    JGs_D{k}.d0 JGs_D{k}.d64 {before} parts JGs_T{k}.source row (by rfl)
    JGs_S{k}0.source (by rfl) JGs_S{k}1.source multiply (by rfl) JGs_D{k}.source JGs_D{k}.finish scaled write
#print axioms source
end AspisR1.{ns}
end
'''
 out[ns]=s
for mod,s in out.items():
 p=R/'lean'/(mod+'.lean')
 if '--check' in sys.argv:assert p.read_text()==s,mod
 else:p.write_text(s)
print(len(out),'successive kind instances')
