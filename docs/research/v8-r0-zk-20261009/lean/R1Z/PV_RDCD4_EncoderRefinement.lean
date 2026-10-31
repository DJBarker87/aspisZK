import R1Z.PV_RDCD4_EncoderNext
open Aeneas Aeneas.Std Result
namespace R1Z.PV_RDCD4_EncoderRefinement
open PV_RDCD4_EncoderLoop
set_option autoImplicit false

/-- Every entered source loop, including step failure/divergence and the
final exhausted next. No callback law is assumed; the final encoder uses the
original CodeField step, not a replacement field dictionary. -/
theorem source {E S : Type} (step : (List E × E) → S → Result S)
    (fuel : Nat) (xs : List E) (it : PV_RDCD4_ArrayIter194.State E)
    (i n : Nat) (acc : S) (hx : xs.length=2*fuel)
    (hr : it.start+fuel=it.stop) (hs : it.stop=it.data.length) :
    loop step (fuel+1) (⟨⟨xs,[]⟩,it,i,n⟩ : Iter E) acc =
      run step ((pairs xs).zip (PV_RDCD4_ArraySuffix.remaining it)) acc := by
  induction fuel generalizing xs it acc with
  | zero =>
    have he : xs=[] := List.eq_nil_of_length_eq_zero (by omega)
    subst xs
    rw [done step _ 0 acc (by rw [PV_RDCD4_EncoderNext.empty])]
    rfl
  | succ fuel ih =>
    cases xs with
    | nil => simp only [List.length_nil] at hx; omega
    | cons a xs =>
      cases xs with
      | nil => simp only [List.length_cons,List.length_nil] at hx; omega
      | cons b tail =>
        have ha : it.start < it.stop := by omega
        obtain ⟨v,hrem,hnext⟩ := PV_RDCD4_ArraySuffix.active it hs ha
        rw [advance step _ _ ([a,b],v) (fuel+1) acc
          (PV_RDCD4_EncoderNext.pair a b v tail it _ i n hnext)]
        rw [hrem]
        change (do
          let acc ← step ([a,b],v) acc
          loop step (fuel+1) (⟨⟨tail,[]⟩,{it with start:=it.start+1},i,n⟩ : Iter E) acc) =
          (do
          let acc ← step ([a,b],v) acc
          run step ((pairs tail).zip
            (PV_RDCD4_ArraySuffix.remaining {it with start:=it.start+1})) acc)
        apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
        intro acc' _
        exact ih tail {it with start:=it.start+1} acc'
          (by simp only [List.length_cons] at hx; omega)
          (by dsimp; omega) hs

#print axioms source
end R1Z.PV_RDCD4_EncoderRefinement
