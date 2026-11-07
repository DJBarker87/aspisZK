import NNG_Tree094
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_EraseTail094
open Aeneas Aeneas.Std Result NMT_tx1 NNG_Context094 NMT_CallTree

theorem markCheckpointWrite {H : Type} (c : Calls) (parent : Parent H) (bytes : alloc.vec.Vec U8) :
 erase (NNG_Tree094.f_markCheckpointWrite c parent bytes)=NNG_Suffix094.f_markCheckpointWrite c parent bytes := by
 unfold NNG_Tree094.f_markCheckpointWrite NNG_Suffix094.f_markCheckpointWrite NNG_Tree094.NNG_call_11
 simp only [Bind.bind]
 rw [erase_bind,erase_invoke]
 apply result_congr
 intro u
 rfl
#print axioms markCheckpointWrite

theorem bytes {H : Type} (c : Calls) (parent : Parent H) (val : verifier.Prepared) (a : verifier.Accumulator) (v : alloc.vec.Vec aspis_core.field.QM31) :
 erase (NNG_Tree094.f_bytes c parent val a v)=NNG_Suffix094.f_bytes c parent val a v := by
 unfold NNG_Tree094.f_bytes NNG_Suffix094.f_bytes NNG_Tree094.NNG_call_6
 simp only [Bind.bind]
 rw [erase_bind,erase_invoke]
 apply result_congr
 intro bytes
 exact markCheckpointWrite c parent bytes
#print axioms bytes

theorem s3 {H : Type} (c : Calls) (parent : Parent H) (val : verifier.Prepared) (a : verifier.Accumulator) (pending : verifier.BatchedWeights) (s2 : Slice aspis_core.field.QM31) (deref_mut_back : Slice aspis_core.field.QM31 → alloc.vec.Vec aspis_core.field.QM31) :
 erase (NNG_Tree094.f_s3 c parent val a pending s2 deref_mut_back)=NNG_Suffix094.f_s3 c parent val a pending s2 deref_mut_back := by
 unfold NNG_Tree094.f_s3 NNG_Suffix094.f_s3 NNG_Tree094.NNG_call_7
 simp only [Bind.bind]
 rw [erase_bind,erase_invoke]
 apply result_congr
 intro after
 exact bytes c parent val a (deref_mut_back after)
#print axioms s3

theorem s2 {H : Type} (c : Calls) (parent : Parent H) (val : verifier.Prepared) (a : verifier.Accumulator) (pending : verifier.BatchedWeights) :
 erase (NNG_Tree094.f_s2 c parent val a pending)=NNG_Suffix094.f_s2 c parent val a pending := by
 unfold NNG_Tree094.f_s2 NNG_Suffix094.f_s2
 simp only [Bind.bind]
 rw [erase_bind,erase_lift]
 apply result_congr
 intro pair
 rcases pair with ⟨s2,back⟩
 exact s3 c parent val a pending s2 back
#print axioms s2

theorem r8 {H : Type} (c : Calls) (parent : Parent H) (g1 : Array aspis_core.field.wide_exact.WideExact 29#usize) (val : verifier.Prepared) (val1 : verifier.Accumulator) (val2 : verifier.QueryGeometry) (val3 : verifier.BatchedWeights) :
 erase (NNG_Tree094.f_r8 c parent g1 val val1 val2 val3)=NNG_Suffix094.f_r8 c parent g1 val val1 val2 val3 := by
 unfold NNG_Tree094.f_r8 NNG_Suffix094.f_r8 NNG_Tree094.NNG_call_4
 simp only [Bind.bind]
 rw [erase_bind,erase_invoke]
 apply result_congr
 intro reply
 cases reply with
 | Err e=>rfl
 | Ok pair=>
   simp only [core.result.Result.Insts.CoreOpsTry.branch,erase_bind,erase_lift,bind_tc_ok]
   exact s2 c parent val pair.1 pair.2
#print axioms r8

theorem r7 {H : Type} (c : Calls) (parent : Parent H) (g1 : Array aspis_core.field.wide_exact.WideExact 29#usize) (val : verifier.Prepared) (val1 : verifier.Accumulator) (val2 : verifier.QueryGeometry) (s1 : Slice aspis_core.field.QM31) :
 erase (NNG_Tree094.f_r7 c parent g1 val val1 val2 s1)=NNG_Suffix094.f_r7 c parent g1 val val1 val2 s1 := by
 unfold NNG_Tree094.f_r7 NNG_Suffix094.f_r7 NNG_Tree094.NNG_call_8
 simp only [Bind.bind]
 rw [erase_bind,erase_invoke]
 apply result_congr
 intro reply
 cases reply with
 | Err e=>rfl
 | Ok pending=>
   simp only [core.result.Result.Insts.CoreOpsTry.branch,erase_bind,erase_lift,bind_tc_ok]
   exact r8 c parent g1 val val1 val2 pending
#print axioms r7

theorem r6 {H : Type} (c : Calls) (parent : Parent H) (g1 : Array aspis_core.field.wide_exact.WideExact 29#usize) (val : verifier.Prepared) (val1 : verifier.Accumulator) :
 erase (NNG_Tree094.f_r6 c parent g1 val val1)=NNG_Suffix094.f_r6 c parent g1 val val1 := by
 unfold NNG_Tree094.f_r6 NNG_Suffix094.f_r6 NNG_Tree094.NNG_call_9
 simp only [Bind.bind]
 rw [erase_bind,erase_invoke]
 apply result_congr
 intro reply
 cases reply with
 | Err e=>rfl
 | Ok geo=>
   simp only [core.result.Result.Insts.CoreOpsTry.branch,erase_bind,erase_lift,bind_tc_ok]
   exact r7 c parent g1 val val1 geo (alloc.vec.Vec.deref val1.weights)
#print axioms r6

end AspisR1.NNG_EraseTail094
