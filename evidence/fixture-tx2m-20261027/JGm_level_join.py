from pathlib import Path
import sys,re
R=Path(__file__).resolve().parents[2]
for t in range(3):
 ns=f'JGm_TX2_Levels{t}';c=5216 if t<2 else 4512
 step=f'(fun state => reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash state JGm_TX2_Supplied.nodes{t} 0#usize 0#usize)'
 s='\n'.join(f'import JGm_TX2_Level{t}_{h:02}' for h in range(18))+f'''\nimport JGm_TX2_HeightTools
import JGm_TX2_Initial
set_option autoImplicit false
noncomputable section
namespace AspisR1.{ns}
open Aeneas Aeneas.Std Result MultiproofConeRef

def PhaseView (height : Nat) (s : reference.Scratch) : Prop := match height with
'''
 for h in range(18):
  text=(R/f'lean/JGm_TX2_Level{t}_{h:02}.lean').read_text()
  cursor=re.search(r'\(view : JGm_TX2_View.View s indices00 values00 (\d+)\)',text)[1]
  s+=f'  | {h} => JGm_TX2_View.View s JGm_TX2_Level{t}_{h:02}.indices00 JGm_TX2_Level{t}_{h:02}.values00 {cursor}\n'
 s+=f'''  | 18 => JGm_TX2_View.View s JGm_TX2_Level{t}_17.indicesOut JGm_TX2_Level{t}_17.valuesOut {c}
  | _ => False

theorem step {{Hash : Type}} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (h : Nat) (bound : h<18) (s : reference.Scratch) (view : PhaseView h s) :
    ∃ out, reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash s
      JGm_TX2_Supplied.nodes{t} 0#usize 0#usize=ok (.Done out) ∧ PhaseView (h+1) out := by
  interval_cases h
'''
 for h in range(18):s+=f'  · exact ⟨_,JGm_TX2_Level{t}_{h:02}.source D hash s view⟩\n'
 s+=f'''#print axioms step

theorem source {{Hash : Type}} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch)
    (view : JGm_TX2_View.View s JGm_TX2_Level{t}_00.indices00 JGm_TX2_Level{t}_00.values00 0) :
    ∃ out, reference.levels (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash s
      JGm_TX2_Supplied.nodes{t} 18#u32=ok (.Done out) ∧
    JGm_TX2_View.View out JGm_TX2_Level{t}_17.indicesOut JGm_TX2_Level{t}_17.valuesOut {c} := by
  obtain ⟨out,run,last⟩ := JGm_TX2_HeightTools.compose {step} 18 PhaseView (step D hash) s view
  refine ⟨out,?_,last⟩
  rw [MultiproofConeLevelIteration.levels_eq_iteration _ _ _ _ (by decide)]
  exact run
#print axioms source

theorem on_scratch {{Hash : Type}} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) :
    ∃ out, reference.levels (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (JGk_TX2_Scratch{t}.s12 s) JGm_TX2_Supplied.nodes{t} 18#u32=ok (.Done out) ∧
    JGm_TX2_View.View out JGm_TX2_Level{t}_17.indicesOut JGm_TX2_Level{t}_17.valuesOut {c} :=
  source D hash _ (JGm_TX2_Initial{t}.source s)
#print axioms on_scratch
end AspisR1.{ns}
end
'''
 out=R/f'lean/{ns}.lean'
 if '--check' in sys.argv:assert out.read_text()==s,ns
 else:out.write_text(s)
print('Generated symbolic phase-indexed native level joins')
