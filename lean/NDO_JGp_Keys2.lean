import RPt_JFq_Queries
import RPz7_Op5T_Concrete
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGp_Keys2
open Aeneas Aeneas.Std Result

def value : Array U64 16#usize := Array.make 16#usize [5983744#u64,9441793#u64,13876482#u64,15737347#u64,13399556#u64,12308229#u64,4197894#u64,11766791#u64,12357896#u64,10227977#u64,0#u64,0#u64,0#u64,0#u64,0#u64,0#u64]

theorem content : Port4B_KeyInstall.keyArray JFq_Queries.value 0 2=value := by
  apply Subtype.ext
  rfl
#print axioms content

theorem source : Port4B_KeyInstall.build JFq_Queries.value 0#usize 10#usize 2#usize=ok value := by
  unfold Port4B_KeyInstall.build
  rw [if_pos rfl]
  have good : (10#usize).val=(OraclePortSelectedDraft.batchPositions 0).length ∧
      (0#usize=0#usize ∨ 0#usize=10#usize) ∧ (2#usize).val<3 := ⟨rfl,Or.inl rfl,by decide⟩
  erw [dif_pos good]
  exact congrArg Result.ok content
#print axioms source
end AspisR1.JGp_Keys2
end
