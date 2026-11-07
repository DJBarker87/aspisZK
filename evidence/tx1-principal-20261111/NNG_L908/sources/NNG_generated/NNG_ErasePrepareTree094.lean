import NNG_PrepareTree094
import NNG_EraseHead094
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ErasePrepareTree094
open Aeneas Aeneas.Std Result NMT_tx1 NNG_Context094 NMT_CallTree
theorem r2 {H : Type} (c : Calls) (parent : Parent H) (g : Array aspis_core.field.wide_exact.WideExact 29#usize) :
 erase (NNG_PrepareTree094.f_r2 c parent g)=NNG_Suffix094.f_r2 c parent g := by
 unfold NNG_PrepareTree094.f_r2 NNG_Suffix094.f_r2 NNG_PrepareTree094.NNG_call_5
 simp only [Bind.bind]
 rw [erase_bind,erase_invoke]
 apply result_congr
 intro pair
 rcases pair with ⟨reply,g1⟩
 cases reply with
 | Err e=>rfl
 | Ok prepared=>
   simp only [core.result.Result.Insts.CoreOpsTry.branch,erase_bind,erase_lift,bind_tc_ok]
   exact NNG_EraseHead094.r3 c parent g1 prepared
#print axioms r2

theorem we {H : Type} (c : Calls) (parent : Parent H) :
 erase (NNG_PrepareTree094.f_we c parent )=NNG_Suffix094.f_we c parent  := by
 unfold NNG_PrepareTree094.f_we NNG_Suffix094.f_we NNG_Tree094.NNG_call_0
 simp only [Bind.bind]
 rw [erase_bind,erase_invoke]
 apply result_congr
 intro wide
 exact r2 c parent (Array.repeat 29#usize wide)
#print axioms we

theorem markParsed {H : Type} (c : Calls) (parent : Parent H) :
 erase (NNG_PrepareTree094.f_markParsed c parent )=NNG_Suffix094.f_markParsed c parent  := by
 unfold NNG_PrepareTree094.f_markParsed NNG_Suffix094.f_markParsed NNG_Tree094.NNG_call_11
 simp only [Bind.bind]
 rw [erase_bind,erase_invoke]
 apply result_congr
 intro u
 exact we c parent
#print axioms markParsed

theorem r1 {H : Type} (c : Calls) (parent : Parent H) :
 erase (NNG_PrepareTree094.f_r1 c parent )=NNG_Suffix094.f_r1 c parent  := by
 unfold NNG_PrepareTree094.f_r1 NNG_Suffix094.f_r1 NNG_Tree094.NNG_call_2
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
 erase (NNG_PrepareTree094.f_r c parent )=NNG_Suffix094.f_r c parent  := by
 unfold NNG_PrepareTree094.f_r NNG_Suffix094.f_r NNG_Tree094.NNG_call_1
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
 erase (NNG_PrepareTree094.f_guard c parent )=NNG_Suffix094.f_guard c parent  := by
 unfold NNG_PrepareTree094.f_guard NNG_Suffix094.f_guard
 dsimp only
 split
 · rfl
 · exact r c parent
#print axioms guard

theorem source {H : Type} (c : Calls) (parent : Parent H) :
 erase (NNG_PrepareTree094.f_guard c parent)=NNG_Context094.body c parent :=
 (guard c parent).trans (NNG_Suffix094.source c parent)
#print axioms source
end AspisR1.NNG_ErasePrepareTree094
