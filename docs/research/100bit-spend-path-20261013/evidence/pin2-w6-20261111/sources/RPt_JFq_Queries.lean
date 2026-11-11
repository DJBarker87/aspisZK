import RPt_JFq_QueryWords
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFq_Queries
open Aeneas Aeneas.Std Result AspisR1Stage2
open JFq_QueryWords
def value : Array U32 22#usize := Array.make 22#usize [46430#u32,76575#u32,251221#u32,185082#u32,132668#u32,55341#u32,88718#u32,248686#u32,152194#u32,172017#u32,86898#u32,117873#u32,189155#u32,110201#u32,151183#u32,177645#u32,179723#u32,126205#u32,162719#u32,101707#u32,156707#u32,243786#u32]
theorem source : T2Nat_QueryReads.queries CheckpointBytes3Reader.raw (JFq_Raw.reader 320#usize)=
    ok (value,JFq_Raw.reader 408#usize) := by
  simp only [T2Nat_QueryReads.queries,raw0,word0,raw1,word1,raw2,word2,raw3,word3,raw4,word4,raw5,word5,raw6,word6,raw7,word7,raw8,word8,raw9,word9,raw10,word10,raw11,word11,raw12,word12,raw13,word13,raw14,word14,raw15,word15,raw16,word16,raw17,word17,raw18,word18,raw19,word19,raw20,word20,raw21,word21,bind_tc_ok,Aeneas.Std.uncurry,lift]
  rfl
#print axioms source
end AspisR1.JFq_Queries
end
