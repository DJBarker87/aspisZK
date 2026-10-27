import sys
from pathlib import Path
R=Path(__file__).resolve().parents[2]
for t in range(3):
 ns=f'JGm_TX2_Levels{t}';c=5216 if t<2 else 4512
 s='\n'.join(f'import JGm_TX2_Level{t}_{h:02}' for h in range(18))+f'''\nimport MultiproofConeLevelIteration
import JGm_TX2_Initial{t}
set_option autoImplicit false
noncomputable section
namespace AspisR1.{ns}
open Aeneas Aeneas.Std Result MultiproofConeRef
'''
 s+='def s00 (s : reference.Scratch) := s\n'
 for h in range(18):s+=f'def s{h+1:02} (s : reference.Scratch) := JGm_TX2_Level{t}_{h:02}.output (s{h:02} s)\n'
 s+=f'''theorem source {{Hash : Type}} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch)
    (view : JGm_TX2_View.View s JGm_TX2_Level{t}_00.indices00 JGm_TX2_Level{t}_00.values00 0) :
    reference.levels (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash s
      JGm_TX2_Supplied.nodes{t} 18#u32=ok (.Done (s18 s)) ∧
    JGm_TX2_View.View (s18 s) JGm_TX2_Level{t}_17.indicesOut JGm_TX2_Level{t}_17.valuesOut {c} := by
'''
 for h in range(18):
  s+=f'  obtain ⟨r{h:02},v{h+1:02}⟩ := JGm_TX2_Level{t}_{h:02}.source D hash (s{h:02} s) '+ ('view' if h==0 else f'v{h:02}')+'\n'
 s+='  refine ⟨?_,v18⟩\n'
 s+=f'''  rw [MultiproofConeLevelIteration.levels_eq_iteration _ _ _ _ (by decide)]
  change MultiproofConeLevelIteration.iterate
    (fun state => reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash state
      JGm_TX2_Supplied.nodes{t} 0#usize 0#usize) 18 (s00 s)=_
  simp only [MultiproofConeLevelIteration.iterate,{','.join('r'+str(h).zfill(2) for h in range(18))},bind_tc_ok]
#print axioms source

theorem on_scratch {{Hash : Type}} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) :
    reference.levels (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (JGk_TX2_Scratch{t}.s12 s) JGm_TX2_Supplied.nodes{t} 18#u32=
        ok (.Done (s18 (JGk_TX2_Scratch{t}.s12 s))) ∧
    JGm_TX2_View.View (s18 (JGk_TX2_Scratch{t}.s12 s)) JGm_TX2_Level{t}_17.indicesOut JGm_TX2_Level{t}_17.valuesOut {c} :=
  source D hash _ (JGm_TX2_Initial{t}.source s)
#print axioms on_scratch
end AspisR1.{ns}
end
'''
 out=Path(__file__).resolve().parent/'JGm_STAGE_PARTS'/f'{ns}.lean.txt'
 if '--check' in sys.argv: assert out.read_text()==s,ns
 else: out.write_text(s)
print('Generated three eighteen-level compositions')
