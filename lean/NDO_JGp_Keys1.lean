import RPt_JFq_Queries
import RPz7_Op5T_Concrete
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGp_Keys1
open Aeneas Aeneas.Std Result

def value : Array U64 16#usize := Array.make 16#usize [23935744#u64,37767425#u64,55506690#u64,62950147#u64,53598980#u64,49233157#u64,16791814#u64,47067911#u64,49431816#u64,40912137#u64,0#u64,0#u64,0#u64,0#u64,0#u64,0#u64]

theorem content : Port4B_KeyInstall.keyArray JFq_Queries.value 0 1=value := by
  apply Subtype.ext
  rfl
#print axioms content

theorem source : Port4B_KeyInstall.build JFq_Queries.value 0#usize 10#usize 1#usize=ok value := by
  unfold Port4B_KeyInstall.build
  rw [if_pos rfl]
  have good : (10#usize).val=(OraclePortSelectedDraft.batchPositions 0).length ∧
      (0#usize=0#usize ∨ 0#usize=10#usize) ∧ (1#usize).val<3 := ⟨rfl,Or.inl rfl,by decide⟩
  erw [dif_pos good]
  exact congrArg Result.ok content
#print axioms source
end AspisR1.JGp_Keys1
end
