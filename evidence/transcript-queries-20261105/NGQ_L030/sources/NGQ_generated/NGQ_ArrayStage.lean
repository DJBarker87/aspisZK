import NGQ_Effects
import NGQ_SamplerArray8
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGQ_ArrayStage
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
abbrev Bytes32 := Array U8 32#usize
abbrev Blocks := Array Bytes32 8#usize

theorem write (a : Blocks) (i : Usize) (x : Bytes32) (hi : i.val<8) :
    Array.update a i x=ok (a.set i x) := by
  obtain ⟨b,call,value⟩ := WP.spec_imp_exists
    (Array.update_spec a i x (by simpa only [Array.length,a.property,show (8#usize).val=8 by rfl] using hi))
  exact call.trans (congrArg ok value)

theorem read_written (a : Blocks) (i : Usize) (x : Bytes32) (hi : i.val<8) :
    Array.index_usize (a.set i x) i=ok x := by
  have h := NGQ_SamplerArray8.read (a.set i x) i hi
  simpa only [Array.set,List.getElem_set_self] using h

theorem mutable (a : Blocks) (i : Usize) (hi : i.val<8) :
    Array.index_mut_usize a i=ok (a.val[i.val]'(by have := a.property; change a.val.length=8 at this; omega),a.set i) := by
  simp only [Array.index_mut_usize,NGQ_SamplerArray8.read a i hi,bind_tc_ok]

/-- Literal one-pair model for a native arbitrary-prestate cut. Both addresses
use the SAME original state; reply1 is a block, reply2 is the next state. -/
def pair {H : Type} (D : aspis_core.Digest32 H) (hash : H) (i : Usize)
    (blocks advances : Blocks) (state : Bytes32) : Result (Blocks × Blocks × Bytes32) := do
  let block ← D.digest hash (Array.to_slice (Array.make 2#usize
    [Array.to_slice state,Array.to_slice (Array.make 1#usize [1#u8])]))
  let blocks ← Array.update blocks i block
  let advance ← D.digest hash (Array.to_slice (Array.make 2#usize
    [Array.to_slice state,Array.to_slice (Array.make 1#usize [2#u8])]))
  let advances ← Array.update advances i advance
  let next ← Array.index_usize advances i
  ok (blocks,advances,next)

theorem pair_result {H : Type} (D : aspis_core.Digest32 H) (hash : H) (i : Usize)
    (blocks advances : Blocks) (state : Bytes32) (hi : i.val<8) :
    pair D hash i blocks advances state=
      (do
        let block ← D.digest hash (Array.to_slice (Array.make 2#usize
          [Array.to_slice state,Array.to_slice (Array.make 1#usize [1#u8])]))
        let advance ← D.digest hash (Array.to_slice (Array.make 2#usize
          [Array.to_slice state,Array.to_slice (Array.make 1#usize [2#u8])]))
        ok (blocks.set i block,advances.set i advance,advance)) := by
  simp only [pair,write _ _ _ hi,read_written _ _ _ hi,bind_tc_ok]

#print axioms write
#print axioms read_written
#print axioms mutable
#print axioms pair_result
end AspisR1.NGQ_ArrayStage
end
