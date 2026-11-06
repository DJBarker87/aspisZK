import NIT_RegularChain
import NJU_WeakPairDomain
import NJU_WeakSharedChain
import NJU_WeakSharedComplete
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJU_WeakRegularChain
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_PairControl
open NIT_RegularChain
variable [FIo_Native.Allocation]

/- Generalized domain only. Original data/trace/evaluator definitions reused. -/
theorem after_interpreted (c : Context) (b : Bool) (parts : Parts) (reply : RU) (out : Result NR)
 (domain : NJU_WeakPairDomain.Domain c.w.value c.alpha.value c.f.value c.kappa)
 (trace : After c b parts reply out) : afterRegular c b parts reply=out := by
 cases trace with
 | rejected e => rfl
 | unshared out isFalse tail =>
  subst b
  change NIT_TailChain.sourceTail _ _ _ _ _ _=out
  rw [NIT_TailChain.source c.w c.f c.ap0 c.ap1 parts c.kappa c.lowAddress domain.s2]
  exact NIT_TailChain.interpreted c.w c.f c.ap0 c.ap1 parts c.kappa c.lowAddress domain.s2
   domain.size domain.extra out tail
 | shared out isTrue tail =>
  subst b
  exact NJU_WeakSharedChain.shared_interpreted c parts out domain tail


theorem after_exists (c : Context) (b : Bool) (parts : Parts) (reply : RU)
 (domain : NJU_WeakPairDomain.Domain c.w.value c.alpha.value c.f.value c.kappa)
 (c0 : canonical c.ap0.value) (c1 : canonical c.ap1.value) (cp : canonical parts) :
 ∃ out,After c b parts reply out := by
 cases reply with
 | Err e => exact ⟨ok (.Err e),.rejected e⟩
 | Ok u =>
  cases u
  cases b with
  | false =>
   obtain ⟨out,tail,_⟩ := NIT_TailChain.complete c.w c.f c.ap0 c.ap1 parts c.kappa c.lowAddress domain.s2
    domain.size c0 c1 domain.extra cp domain.kappa
   exact ⟨out,.unshared out rfl tail⟩
  | true =>
   obtain ⟨out,tail,_⟩ := NJU_WeakSharedComplete.complete c parts domain c0 c1 cp
   exact ⟨out,.shared out rfl tail⟩


theorem interpreted [FIo_Native.Allocation] (c : Context) (scratch : Scratch) (out : Result NR)
 (domain : NJU_WeakPairDomain.Domain c.w.value c.alpha.value c.f.value c.kappa)
 (trace : Trace c scratch out) : regular c scratch=out := by
 have guard := (NIT_ControlCuts.guard c.w.value).1
 cases trace with
 | failed e call => simp only [uncurry,regular,guard,call,bind_tc_ok];rfl
 | diverged call => simp only [uncurry,regular,guard,call,bind_tc_ok];rfl
 | returned reply after parts out call tail =>
  simp only [uncurry,regular,guard,call,bind_tc_ok]
  exact after_interpreted c _ parts reply out domain tail


theorem complete [FIo_Native.Allocation] (c : Context) (scratch : Scratch)
 (domain : NJU_WeakPairDomain.Domain c.w.value c.alpha.value c.f.value c.kappa)
 (c0 : canonical c.ap0.value) (c1 : canonical c.ap1.value)
 (inv : NHX_RegularPost.Inv scratch initial) :
 ∃ out,Trace c scratch out ∧ regular c scratch=out := by
 have result : ∃ out,Trace c scratch out := by
  cases call : FIo_Native.weights.process_regular_kinds c.w.value (NGM_GuardExact.guard c.w.value 2#usize)
   c.alpha.value.to_slice c.f.value 2#usize 64#usize c.ap0.value c.ap1.value scratch initial with
  | fail e => exact ⟨fail e,.failed e call⟩
  | div => exact ⟨div,.diverged call⟩
  | ok result =>
   rcases result with ⟨reply,after,parts⟩
   have post := NIG_PairFrames.regular c.w.value _ c.alpha.value.to_slice c.f.value c.ap0.value c.ap1.value
    domain.s2 domain.factors c0 c1 scratch after initial parts reply inv call
   obtain ⟨out,tail⟩ := after_exists c _ parts reply domain c0 c1 post.2.2
   exact ⟨out,.returned reply after parts out call tail⟩
 obtain ⟨out,trace⟩ := result
 exact ⟨out,trace,interpreted c scratch out domain trace⟩


#print axioms after_interpreted
#print axioms after_exists
#print axioms interpreted
#print axioms complete
end AspisR1.NJU_WeakRegularChain
