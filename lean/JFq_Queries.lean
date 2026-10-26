import JFq_QueryWords
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFq_Queries
open Aeneas Aeneas.Std Result AspisR1Stage2
open JFq_QueryWords
def value : Array U32 22#usize := Array.make 22#usize [93499#u32,147529#u32,216823#u32,245899#u32,209371#u32,192317#u32,65593#u32,183859#u32,193093#u32,159813#u32,132355#u32,218094#u32,178080#u32,149624#u32,166165#u32,42158#u32,179622#u32,21248#u32,63860#u32,55377#u32,185637#u32,14297#u32]
theorem source : T2Nat_QueryReads.queries CheckpointBytes3Reader.raw (JFq_Raw.reader 320#usize)=
    ok (value,JFq_Raw.reader 408#usize) := by
  simp only [T2Nat_QueryReads.queries,raw0,word0,raw1,word1,raw2,word2,raw3,word3,raw4,word4,raw5,word5,raw6,word6,raw7,word7,raw8,word8,raw9,word9,raw10,word10,raw11,word11,raw12,word12,raw13,word13,raw14,word14,raw15,word15,raw16,word16,raw17,word17,raw18,word18,raw19,word19,raw20,word20,raw21,word21,bind_tc_ok,Aeneas.Std.uncurry,lift]
  rfl
#print axioms source
end AspisR1.JFq_Queries
end
