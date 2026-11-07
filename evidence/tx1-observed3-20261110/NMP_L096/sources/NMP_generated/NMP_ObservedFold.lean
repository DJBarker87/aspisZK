import NMP_ObservedStep0
import NMP_ObservedStep1
import NMP_ObservedStep2
import NMP_ObservedStep3
import NMP_ObservedStep4
import NMP_ObservedStep5
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMP_ObservedSteps
open Aeneas Aeneas.Std Result NMP_prepare NMP_Emitted
open NMT_CallTree (Code invoke erase)
/-- Exact full-Result source-order fold. This is emitted-body support, not a
physical RowSpec or a replacement for the SAME-argument child installations. -/
theorem emitted {H W : Type} (c : Calls) (s : Parent H W) :
 erase (body c s) = observed c s := by
 unfold body execute step observed NMP_prepare.r1_semantic.verify_observed
 simp only [NMT_CallTree.erase_bind,NMT_CallTree.erase_invoke,NMT_CallTree.erase_pure]
 cases hp : c.c6 s.bytes with
 | fail e => simp only [hp,bind_tc_fail]
 | div => simp only [hp,bind_tc_div]
 | ok p =>
  cases p with
  | Err e => rfl
  | Ok p =>
   cases hm : c.c8 s.observer 0#u8 with
   | fail e => simp only [hm,hp,bind_tc_ok,bind_tc_fail]
   | div => simp only [hm,hp,bind_tc_ok,bind_tc_div]
   | ok u =>
    cases u
    cases ht : c.c9 s.digest s.publicValue s.hash p.c1_root with
    | fail e => simp only [hm,hp,ht,bind_tc_ok,bind_tc_fail]
    | div => simp only [hm,hp,ht,bind_tc_ok,bind_tc_div]
    | ok t =>
     cases t with
     | Err e => rfl
     | Ok t =>
      cases hb : c.c5 s.digest p t with
      | fail e => simp only [hm,hp,ht,hb,bind_tc_ok,bind_tc_fail]
      | div => simp only [hm,hp,ht,hb,bind_tc_ok,bind_tc_div]
      | ok pair =>
       rcases pair with ⟨ch,after⟩
       cases ch with
       | Err e => rfl
       | Ok ch =>
        cases hm1 : c.c8 s.observer 1#u8 with
        | fail e => simp only [hm,hp,ht,hb,hm1,bind_tc_ok,bind_tc_fail]
        | div => simp only [hm,hp,ht,hb,hm1,bind_tc_ok,bind_tc_div]
        | ok u =>
         cases u
         simp only [hm,hp,ht,hb,hm1,bind_tc_ok,NMT_CallTree.result_right]
#print axioms emitted
end AspisR1.NMP_ObservedSteps
