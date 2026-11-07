import NNG_EraseMiddle094
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_EraseHead094
open Aeneas Aeneas.Std Result NMT_tx1 NNG_Context094 NMT_CallTree

theorem markPrepare {H : Type} (c : Calls) (parent : Parent H) (g1 : Array aspis_core.field.wide_exact.WideExact 29#usize) (val : verifier.Prepared) (val1 : verifier.Accumulator) :
 erase (NNG_Tree094.f_markPrepare c parent g1 val val1)=NNG_Suffix094.f_markPrepare c parent g1 val val1 := by
 unfold NNG_Tree094.f_markPrepare NNG_Suffix094.f_markPrepare NNG_Tree094.NNG_call_11
 simp only [Bind.bind]
 rw [erase_bind,erase_invoke]
 apply result_congr
 intro u
 exact NNG_EraseMiddle094.i c parent g1 val val1
#print axioms markPrepare

theorem r3 {H : Type} (c : Calls) (parent : Parent H) (g1 : Array aspis_core.field.wide_exact.WideExact 29#usize) (val : verifier.Prepared) :
 erase (NNG_Tree094.f_r3 c parent g1 val)=NNG_Suffix094.f_r3 c parent g1 val := by
 unfold NNG_Tree094.f_r3 NNG_Suffix094.f_r3 NNG_Tree094.NNG_call_10
 simp only [Bind.bind]
 rw [erase_bind,erase_invoke]
 apply result_congr
 intro reply
 cases reply with
 | Err e=>rfl
 | Ok acc=>
   simp only [core.result.Result.Insts.CoreOpsTry.branch,erase_bind,erase_lift,bind_tc_ok]
   exact markPrepare c parent g1 val acc
#print axioms r3

theorem r2 {H : Type} (c : Calls) (parent : Parent H) (g : Array aspis_core.field.wide_exact.WideExact 29#usize) :
 erase (NNG_Tree094.f_r2 c parent g)=NNG_Suffix094.f_r2 c parent g := by
 unfold NNG_Tree094.f_r2 NNG_Suffix094.f_r2 NNG_Tree094.NNG_call_5
 simp only [Bind.bind]
 rw [erase_bind,erase_invoke]
 apply result_congr
 intro pair
 rcases pair with ⟨reply,g1⟩
 cases reply with
 | Err e=>rfl
 | Ok prepared=>
   simp only [core.result.Result.Insts.CoreOpsTry.branch,erase_bind,erase_lift,bind_tc_ok]
   exact r3 c parent g1 prepared
#print axioms r2

theorem we {H : Type} (c : Calls) (parent : Parent H) :
 erase (NNG_Tree094.f_we c parent )=NNG_Suffix094.f_we c parent  := by
 unfold NNG_Tree094.f_we NNG_Suffix094.f_we NNG_Tree094.NNG_call_0
 simp only [Bind.bind]
 rw [erase_bind,erase_invoke]
 apply result_congr
 intro wide
 exact r2 c parent (Array.repeat 29#usize wide)
#print axioms we

theorem markParsed {H : Type} (c : Calls) (parent : Parent H) :
 erase (NNG_Tree094.f_markParsed c parent )=NNG_Suffix094.f_markParsed c parent  := by
 unfold NNG_Tree094.f_markParsed NNG_Suffix094.f_markParsed NNG_Tree094.NNG_call_11
 simp only [Bind.bind]
 rw [erase_bind,erase_invoke]
 apply result_congr
 intro u
 exact we c parent
#print axioms markParsed

theorem r1 {H : Type} (c : Calls) (parent : Parent H) :
 erase (NNG_Tree094.f_r1 c parent )=NNG_Suffix094.f_r1 c parent  := by
 unfold NNG_Tree094.f_r1 NNG_Suffix094.f_r1 NNG_Tree094.NNG_call_2
 simp only [Bind.bind]
 rw [erase_bind,erase_invoke]
 apply result_congr
 intro reply
 cases reply with
 | Err e=>rfl
 | Ok u=>
   simp only [core.result.Result.Insts.CoreOpsTry.branch,erase_bind,erase_lift,bind_tc_ok]
   exact markParsed c parent
#print axioms r1

theorem r {H : Type} (c : Calls) (parent : Parent H) :
 erase (NNG_Tree094.f_r c parent )=NNG_Suffix094.f_r c parent  := by
 unfold NNG_Tree094.f_r NNG_Suffix094.f_r NNG_Tree094.NNG_call_1
 simp only [Bind.bind]
 rw [erase_bind,erase_invoke]
 apply result_congr
 intro reply
 cases reply with
 | Err e=>rfl
 | Ok variant=>
   simp only [core.result.Result.Insts.CoreOpsTry.branch,erase_bind,erase_lift,bind_tc_ok]
   exact r1 c parent
#print axioms r

theorem guard {H : Type} (c : Calls) (parent : Parent H) :
 erase (NNG_Tree094.f_guard c parent )=NNG_Suffix094.f_guard c parent  := by
 unfold NNG_Tree094.f_guard NNG_Suffix094.f_guard
 split
 · rfl
 · exact r c parent
#print axioms guard

theorem source {H : Type} (c : Calls) (parent : Parent H) :
 erase (NNG_Tree094.f_guard c parent)=NNG_Context094.body c parent :=
 (guard c parent).trans (NNG_Suffix094.source c parent)
#print axioms source
end AspisR1.NNG_EraseHead094
