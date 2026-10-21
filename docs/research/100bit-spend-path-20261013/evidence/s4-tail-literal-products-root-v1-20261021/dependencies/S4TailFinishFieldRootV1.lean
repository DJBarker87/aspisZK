import S4TailFieldProductRootV1
import S4TailFinishSourceMapV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FastDotsTailFinishFieldRootV1
open AspisR1FastDotsPushProductTraceRootV1
open AspisR1FastDotsTailFieldProductRootV1
open AspisR1FastDotsTailFinishSourceMapV1

/-- The exact eight-word source finish residue equality determines the
returned Wide field value. No source success or canonicality premise is
added to the already returned residue equality. -/
theorem finish_words_decode_state (s : State) (out : Wide)
    (hwords : (currentFinishWords out).map (fun w=>w.val) =
      ((s.c0.sums.val ++ s.c1.sums.val).map
        (fun x=>x.val % AspisV8R17.RawReducer.P))) :
    AspisR1CurrentWide.Proof.decodeWide
      (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE out) =
      decodeState (stateValue s) := by
  cases s with
  | mk c0 c1 count =>
    cases c0 with
    | mk s0 =>
      cases c1 with
      | mk s1 =>
        obtain ⟨a,b,c,d,hshape0⟩ := List.length_eq_four.mp s0.property
        obtain ⟨e,f,g,h,hshape1⟩ := List.length_eq_four.mp s1.property
        rw [hshape0,hshape1] at hwords
        simp only [currentFinishWords,List.map_append,List.map_cons,List.map_nil,
          List.append_nil,List.cons_append,List.nil_append] at hwords
        injection hwords with ha hrest0
        injection hrest0 with hb hrest1
        injection hrest1 with hc hrest2
        injection hrest2 with hd hrest3
        injection hrest3 with he hrest4
        injection hrest4 with hf hrest5
        injection hrest5 with hg hrest6
        injection hrest6 with hh hrest7
        rw [current_decode_eq]
        apply QuadraticAlgebra.ext <;>
          simp [wideDecoded,qmDecoded,decodeState,stateValue,tupleToTowerQ,
            AspisR1EbyKPushDecodedProductUpdate.castSums,
            hshape0,hshape1,ha,hb,hc,hd,he,hf,hg,hh,
            AspisV8R17.QM31WordTower.decodeQ,AspisV8R17.QM31WordTower.decodeC,
            AspisV8R17.QM31WordTower.embedQ,AspisV8R17.QM31WordTower.embedC,
            AspisV8R17.QM31WordResidues.decodeQ,AspisV8R17.QM31WordResidues.decodeC,
            ZMod.natCast_mod]

/-- Combines precisely the product fold and residue facts returned by the
same callback into its tail's field product sum. -/
theorem finish_is_ordered_field_product_sum (s : State) (out : Wide)
    (ps : List (Wide × QM))
    (hproduct : stateValue s = ps.foldl addProduct
      (stateValue EbyKNewToPushStateABI.pushZero))
    (hwords : (currentFinishWords out).map (fun w=>w.val) =
      ((s.c0.sums.val ++ s.c1.sums.val).map
        (fun x=>x.val % AspisV8R17.RawReducer.P))) :
    AspisR1CurrentWide.Proof.decodeWide
      (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE out) = productSum ps :=
  (finish_words_decode_state s out hwords).trans
    (decoded_tail_product_sum s ps hproduct)

#print axioms finish_words_decode_state
#print axioms finish_is_ordered_field_product_sum
end AspisR1FastDotsTailFinishFieldRootV1
