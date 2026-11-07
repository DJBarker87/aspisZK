import NNG_EraseTail094
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_EraseMiddle094
open Aeneas Aeneas.Std Result NMT_tx1 NNG_Context094 NMT_CallTree

theorem markMerkle {H : Type} (c : Calls) (parent : Parent H) (g1 : Array aspis_core.field.wide_exact.WideExact 29#usize) (val : verifier.Prepared) (val1 : verifier.Accumulator) :
 erase (NNG_Tree094.f_markMerkle c parent g1 val val1)=NNG_Suffix094.f_markMerkle c parent g1 val val1 := by
 unfold NNG_Tree094.f_markMerkle NNG_Suffix094.f_markMerkle NNG_Tree094.NNG_call_11
 simp only [Bind.bind]
 rw [erase_bind,erase_invoke]
 apply result_congr
 intro u
 exact NNG_EraseTail094.r6 c parent g1 val val1
#print axioms markMerkle

theorem r5 {H : Type} (c : Calls) (parent : Parent H) (g1 : Array aspis_core.field.wide_exact.WideExact 29#usize) (val : verifier.Prepared) (val1 : verifier.Accumulator) (folded_root : Array U8 32#usize) :
 erase (NNG_Tree094.f_r5 c parent g1 val val1 folded_root)=NNG_Suffix094.f_r5 c parent g1 val val1 folded_root := by
 unfold NNG_Tree094.f_r5 NNG_Suffix094.f_r5 NNG_Tree094.NNG_call_3
 simp only [Bind.bind]
 rw [erase_bind,erase_invoke]
 apply result_congr
 intro reply
 cases reply with
 | Err e=>rfl
 | Ok u=>
   simp only [core.result.Result.Insts.CoreOpsTry.branch,erase_bind,erase_lift,bind_tc_ok]
   exact markMerkle c parent g1 val val1
#print axioms r5

theorem folded_root {H : Type} (c : Calls) (parent : Parent H) (g1 : Array aspis_core.field.wide_exact.WideExact 29#usize) (val : verifier.Prepared) (val1 : verifier.Accumulator) (r4 : core.result.Result (Array U8 32#usize) core.array.TryFromSliceError) :
 erase (NNG_Tree094.f_folded_root c parent g1 val val1 r4)=NNG_Suffix094.f_folded_root c parent g1 val val1 r4 := by
 unfold NNG_Tree094.f_folded_root NNG_Suffix094.f_folded_root
 simp only [Bind.bind]
 rw [erase_bind,erase_lift]
 apply result_congr
 intro root
 exact r5 c parent g1 val val1 root
#print axioms folded_root

theorem r4 {H : Type} (c : Calls) (parent : Parent H) (g1 : Array aspis_core.field.wide_exact.WideExact 29#usize) (val : verifier.Prepared) (val1 : verifier.Accumulator) (s : Slice U8) :
 erase (NNG_Tree094.f_r4 c parent g1 val val1 s)=NNG_Suffix094.f_r4 c parent g1 val val1 s := by
 unfold NNG_Tree094.f_r4 NNG_Suffix094.f_r4
 simp only [Bind.bind]
 rw [erase_bind,erase_lift]
 apply result_congr
 intro reply
 exact folded_root c parent g1 val val1 reply
#print axioms r4

theorem s {H : Type} (c : Calls) (parent : Parent H) (g1 : Array aspis_core.field.wide_exact.WideExact 29#usize) (val : verifier.Prepared) (val1 : verifier.Accumulator) (i : Usize) (i1 : Usize) :
 erase (NNG_Tree094.f_s c parent g1 val val1 i i1)=NNG_Suffix094.f_s c parent g1 val val1 i i1 := by
 unfold NNG_Tree094.f_s NNG_Suffix094.f_s
 simp only [Bind.bind]
 rw [erase_bind,erase_lift]
 apply result_congr
 intro slice
 exact r4 c parent g1 val val1 slice
#print axioms s

theorem i1 {H : Type} (c : Calls) (parent : Parent H) (g1 : Array aspis_core.field.wide_exact.WideExact 29#usize) (val : verifier.Prepared) (val1 : verifier.Accumulator) (i : Usize) :
 erase (NNG_Tree094.f_i1 c parent g1 val val1 i)=NNG_Suffix094.f_i1 c parent g1 val val1 i := by
 unfold NNG_Tree094.f_i1 NNG_Suffix094.f_i1
 simp only [Bind.bind]
 rw [erase_bind,erase_lift]
 apply result_congr
 intro at1
 exact s c parent g1 val val1 i at1
#print axioms i1

theorem i {H : Type} (c : Calls) (parent : Parent H) (g1 : Array aspis_core.field.wide_exact.WideExact 29#usize) (val : verifier.Prepared) (val1 : verifier.Accumulator) :
 erase (NNG_Tree094.f_i c parent g1 val val1)=NNG_Suffix094.f_i c parent g1 val val1 := by
 unfold NNG_Tree094.f_i NNG_Suffix094.f_i
 simp only [Bind.bind]
 rw [erase_bind,erase_lift]
 apply result_congr
 intro at0
 exact i1 c parent g1 val val1 at0
#print axioms i

end AspisR1.NNG_EraseMiddle094
