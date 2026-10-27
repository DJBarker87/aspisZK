import R1Z.PV_CB3_Array32
import R1Z.PV_CB3_ByteGroups
set_option autoImplicit false
namespace R1Z.PV_CB3_StagedWords
open Aeneas Aeneas.Std Result
open PV_CB3_ByteGroups
theorem length (block : Array U8 32#usize) : (groups block.val).length = 8 := by
  obtain ⟨a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24,a25,a26,a27,a28,a29,a30,a31,h⟩ := PV_CB3_Array32.view block
  subst block
  rfl

def words (block : Array U8 32#usize) : Array U32 8#usize :=
  ⟨groups block.val,length block⟩

theorem source (block : Array U8 32#usize) :
    PV_CB3_StagedSource.staged_reference.words block = ok (words block) := by
  obtain ⟨a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24,a25,a26,a27,a28,a29,a30,a31,h⟩ := PV_CB3_Array32.view block
  subst block
  rfl

theorem value (block : Array U8 32#usize) :
    PV_CB3_SamplerCarry.value PV_CB3_SamplerWord.radix ((words block).val.map UScalar.val) =
      PV_CB3_SamplerCarry.value 256 (block.val.map UScalar.val) := by
  exact group_value block.val (by rw [block.property]; rfl)
#print axioms length
#print axioms source
#print axioms value
end R1Z.PV_CB3_StagedWords
