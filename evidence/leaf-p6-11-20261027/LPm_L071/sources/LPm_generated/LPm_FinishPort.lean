import LPm_PublicPort
set_option autoImplicit false
namespace AspisR1.LPm_FinishPort
open Aeneas Aeneas.Std Result LPi_FieldValues LPm_RawPort
abbrev E := AspisR1CurrentPreparedClaim.Concrete.E

def words (x : E) : List U32 :=
  [x.c0.c0.a,x.c0.c0.b,x.c0.c1.a,x.c0.c1.b,
   x.c1.c0.a,x.c1.c0.b,x.c1.c1.a,x.c1.c1.b]

theorem words_injective (x y : E) (same : words x=words y) : x=y := by
  rcases x with ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,⟨⟨e,f⟩,⟨g,h⟩⟩⟩
  rcases y with ⟨⟨⟨i,j⟩,⟨k,l⟩⟩,⟨⟨m,n⟩,⟨o,p⟩⟩⟩
  simp only [words,List.cons.injEq,and_true] at same
  rcases same with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  rfl

theorem from_finish_words (x : AspisR1CurrentPreparedClaim.ClaimParser.FinishE) :
    words (AspisR1CurrentPreparedClaim.ClaimParser.fromFinish x)=
      AspisR1FinishDotSourceABI.finishWords x := rfl

#print AspisR1EbyKFinish.Proof.word

theorem word_eq (r : U64) (v : U32) (value : v.val=r.val%2147483647) :
    v=AspisR1EbyKFinish.Proof.word r := by
  apply UScalar.eq_of_val_eq
  rw [value]
  rfl

/-- Complete native finalizer return equals the retained concrete cohort
finalizer after the explicit eight-word owner port. -/
theorem source (s : Native) : ∃ out,
    FIo_Native.fast_pairing.EbyKDot.finish s=ok out ∧
    (AspisR1S5ClaimDotConcreteAdapter.concreteOps AspisR1EbyKPushDecodedProductUpdate.QRaw).finishDot
      (statePort s)=ok (ePort out) := by
  obtain ⟨out,native,h0,h1,h2,h3,h4,h5,h6,h7⟩ := LPf_PublicDotAllStates.source s
  obtain ⟨finish,call,_,layout⟩ := AspisR1FinishDotSourceABI.finishFromPush_total (statePort s)
  have w0 := word_eq _ _ h0
  have w1 := word_eq _ _ h1
  have w2 := word_eq _ _ h2
  have w3 := word_eq _ _ h3
  have w4 := word_eq _ _ h4
  have w5 := word_eq _ _ h5
  have w6 := word_eq _ _ h6
  have w7 := word_eq _ _ h7
  have same : AspisR1CurrentPreparedClaim.ClaimParser.fromFinish finish=ePort out := by
    apply words_injective
    rw [from_finish_words,layout]
    obtain ⟨a,b,c,d,left⟩ := LPf_ArrayFour.shape s.c0.sums
    obtain ⟨e,f,g,h,right⟩ := LPf_ArrayFour.shape s.c1.sums
    simp only [statePort,left,right,Array.make,List.cons_append,List.nil_append,
      List.map_cons,List.map_nil,words,ePort,qPort,w0,w1,w2,w3,w4,w5,w6,w7]
    rfl
  refine ⟨out,native,?_⟩
  change (do let finish ← AspisR1FinishDotSourceABI.finishFromPush (statePort s)
             ok (AspisR1CurrentPreparedClaim.ClaimParser.fromFinish finish))=ok (ePort out)
  rw [call,bind_tc_ok,same]

#print axioms words_injective
#print axioms from_finish_words
#print axioms word_eq
#print axioms source
end AspisR1.LPm_FinishPort
