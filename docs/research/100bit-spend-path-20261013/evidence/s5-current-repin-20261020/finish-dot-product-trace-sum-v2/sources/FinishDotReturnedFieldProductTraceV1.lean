import AspisR1FinishDotReturnedFieldProductV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FinishDotReturnedFieldProductTraceV1
open AspisR1FinishDotDecodedProductTrace
open AspisR1FinishDotReturnedDeltaDecodeV1
open AspisR1FinishDotReturnedProductWords AspisR1FinishDotReturnedFieldProductV1
open AspisR1FinishRelationCurrent AspisR1FinishDotConcreteOps

/-- The successful caller exposes the exact ordered field/weight reads used by
its dot updates, and its returned value is the field product sum over those
same reads. -/
theorem successful_finish_ordered_field_product_trace {W : Type}
    (ops : AspisR1FinishRelationCurrent.FinishOps W PushState)
    (fm : Slice U8) (ws : Slice FinishQM) (out : FinishE)
    (hrun : verifier.finish_query_dot
      (withConcreteDot (AspisR1CurrentWide.Proof.finishConcreteField ops)
        AspisR1EbyKPushDecodedProductUpdate.QRaw) fm ws = .ok (.Ok out)) :
    ∃ xs : List (Usize × FinishE × FinishQM),
      xs.length = ws.len.val ∧
      (∀ k (hk : k < xs.length), (xs[k]'hk).1.val = k) ∧
      (∀ t ∈ xs, t.1 < ws.len ∧
        AspisR1CurrentWide.Proof.finishField fm t.1 = .ok t.2.1 ∧
        Slice.index_usize ws t.1 = .ok t.2.2) ∧
      AspisR1CurrentWide.Proof.decodeFinish out = productSum xs := by
  obtain ⟨final,xs,hfinish,hwords,hdelta,hlen,hseq,hreads⟩ :=
    AspisR1FinishDotReturnedProductWords.successful_current_finish_query_product_words
      ops fm ws out hrun
  cases final with
  | mk c0 c1 count =>
    cases c0 with
    | mk s0 =>
      cases c1 with
      | mk s1 =>
        obtain ⟨a,b,c,d,hshape0⟩ := List.length_eq_four.mp s0.property
        obtain ⟨e,f,g,h,hshape1⟩ := List.length_eq_four.mp s1.property
        have hvals := congrArg (List.map (fun w : U32 => w.val)) hwords
        rw [hshape0,hshape1] at hvals
        simp only [AspisR1FinishDotSourceABI.finishWords,
          List.map_map,Function.comp_def,List.map_append,List.map_cons,List.map_nil,
          AspisR1EbyKFinish.Proof.word,
          AspisR1CanonicalDotFinish.Proof.canonicalWord_val,
          List.append_nil] at hvals
        injection hvals with ha htail0
        injection htail0 with hb htail1
        injection htail1 with hc htail2
        injection htail2 with hd htail3
        injection htail3 with he htail4
        injection htail4 with hf htail5
        injection htail5 with hg htail6
        injection htail6 with hh htail7
        have hlow :
            AspisV8R17.QM31WordTower.decodeQ
                (AspisR1FinishDotReturnedProductWords.finishQMWords out.c0) =
              tupleToTowerQ (AspisR1EbyKPushDecodedProductUpdate.castSums s0) := by
          simp [AspisR1FinishDotReturnedProductWords.finishQMWords,
            tupleToTowerQ,AspisR1EbyKPushDecodedProductUpdate.castSums,
            hshape0,ha,hb,hc,hd,AspisV8R17.QM31WordTower.decodeQ,
            AspisV8R17.QM31WordTower.decodeC,AspisV8R17.QM31WordTower.embedQ,
            AspisV8R17.QM31WordTower.embedC,AspisV8R17.QM31WordResidues.decodeQ,
            AspisV8R17.QM31WordResidues.decodeC,ZMod.natCast_mod]
        have hhigh :
            AspisV8R17.QM31WordTower.decodeQ
                (AspisR1FinishDotReturnedProductWords.finishQMWords out.c1) =
              tupleToTowerQ (AspisR1EbyKPushDecodedProductUpdate.castSums s1) := by
          simp [AspisR1FinishDotReturnedProductWords.finishQMWords,
            tupleToTowerQ,AspisR1EbyKPushDecodedProductUpdate.castSums,
            hshape1,he,hf,hg,hh,AspisV8R17.QM31WordTower.decodeQ,
            AspisV8R17.QM31WordTower.decodeC,AspisV8R17.QM31WordTower.embedQ,
            AspisV8R17.QM31WordTower.embedC,AspisV8R17.QM31WordResidues.decodeQ,
            AspisV8R17.QM31WordResidues.decodeC,ZMod.natCast_mod]
        have hdecode := AspisR1FinishDotReturnedDecodedValueV1.decodeFinish_eq_word_tower out
        let final' : PushState := ⟨⟨s0⟩,⟨s1⟩,count⟩
        have hfinal : AspisR1CurrentWide.Proof.decodeFinish out =
            decodeDelta (stateDelta final') := by
          rw [hdecode]
          simp [decodeDelta,stateDelta,hlow,hhigh,final']
        have hdelta' : stateDelta final' = deltaSum xs := by
          simpa [final'] using hdelta
        rw [hdelta'] at hfinal
        refine ⟨xs,hlen,hseq,hreads,?_⟩
        exact hfinal.trans (AspisR1FinishDotReturnedFieldProductV1.decodeDelta_sum xs)

#print axioms successful_finish_ordered_field_product_trace
end AspisR1FinishDotReturnedFieldProductTraceV1
