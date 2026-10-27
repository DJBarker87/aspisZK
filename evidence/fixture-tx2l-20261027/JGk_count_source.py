from pathlib import Path
R=Path(__file__).resolve().parents[2]
s='''import JGk_TX2_ScratchIndices
import Port4B_CountInstall
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGk_TX2_CountSource
open Aeneas Aeneas.Std Result
'''
for t in range(3):
 count=141 if t==2 else 163;keyt=2 if t==2 else 0
 s+=f'''def front{t} (s : MultiproofConeRef.reference.Scratch) : Slice U32 :=
  ⟨(JGk_TX2_Scratch{t}.s12 s).idx.val.take 12,by
    have bound := List.length_take_le 12 (JGk_TX2_Scratch{t}.s12 s).idx.val
    scalar_tac⟩
theorem raw{t} (s : MultiproofConeRef.reference.Scratch) :
    (front{t} s).val.map UScalar.val=JGf_TX2_Count{keyt}.indices00 := by
  change ((JGk_TX2_Scratch{t}.s12 s).idx.val.take 12).map UScalar.val=_
  rw [JGk_TX2_ScratchIndices.front{t}_12]
  rfl
#print axioms raw{t}
theorem well{t} (s : MultiproofConeRef.reference.Scratch) :
    OraclePortFrozenOrder.wellFormed ((front{t} s).val.map UScalar.val) := by
  rw [raw{t}]
  refine ⟨by decide,by decide,by decide,?_⟩
  intro i hi
  simp only [JGf_TX2_Count{keyt}.indices00,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
#print axioms well{t}
theorem source{t} (s : MultiproofConeRef.reference.Scratch) :
    Port4B_Install.leaves.op11 .Two (front{t} s)=ok (some {count}#usize) := by
  change Port4B_CountInstall.nodeCount .Two (front{t} s)=_
  unfold Port4B_CountInstall.nodeCount
  rw [dif_pos (well{t} s)]
  have value : Port4B_CountInstall.countValue ((front{t} s).val.map UScalar.val) (well{t} s)={count}#usize := by
    apply UScalar.eq_of_val_eq
    change MultiproofConeCountLevels.sourceCount 18 ((front{t} s).val.map UScalar.val)={count}
    rw [raw{t},JGf_TX2_Count{keyt}.total00]
  rw [value]
#print axioms source{t}
'''
s+='end AspisR1.JGk_TX2_CountSource\nend\n'
(R/'lean/JGk_TX2_CountSource.lean').write_text(s)
