import R1Z.PV_RunJoin_QueryLeafRows64
import R1Z.PV_RunJoin_QueryLaneTotal64
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_QueryLeafWordBounds64
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]

theorem last_index :
    (Usize.wrapping_add (Usize.wrapping_mul 4#usize 262143#usize) 3#usize).val=1048575 := by
  rw [Usize.wrapping_add_val_eq,PV_RunJoin_QueryLaneTotal64.first 262143#usize (by decide)]
  change (4*262143+3)%UScalar.size .Usize=1048575
  rw [Nat.mod_eq_of_lt (by have h := PV_RunJoin_SamplerByteIndices54.size;omega)]

theorem complete (words : Slice host_commitment.Word) (lanes : Slice Usize)
    (small : lanes.length≤29) (out : Array U8 480#usize × Usize)
    (success : host_commitment.commitment_leaf_bytes words lanes 262143#usize=ok out)
    (j : Usize) (bound : j.val<lanes.length) :
    ∃ word, Slice.index_usize words j=ok word ∧ 1048576≤PV_RunJoin_QueryWordTotal64.length word := by
  obtain ⟨bytes,at1,result,hr⟩ := PV_RunJoin_QueryLeafRows64.last_row words lanes 262143#usize out success
  obtain ⟨word,value,hword,hvalue⟩ := PV_RunJoin_QueryLeafChannel64.visited words lanes
    262143#usize 3#usize small bytes at1 0#usize j result (by change 0≤j.val;omega) bound hr
  have h := PV_RunJoin_QueryReadBounds64.word word _ value hvalue
  rw [last_index] at h
  exact ⟨word,hword,by omega⟩

#print axioms last_index
#print axioms complete
end R1Z.PV_RunJoin_QueryLeafWordBounds64
