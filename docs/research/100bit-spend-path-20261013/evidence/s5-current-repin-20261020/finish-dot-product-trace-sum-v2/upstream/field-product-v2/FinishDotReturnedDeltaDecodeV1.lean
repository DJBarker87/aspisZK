import AspisR1FinishDotReturnedDecodedValueV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FinishDotReturnedDeltaDecodeV1
open AspisR1FinishDotDecodedProductTrace AspisR1FinishDotConcreteOps
open AspisR1FinishDotReturnedProductWords AspisR1FinishRelationCurrent

abbrev M := AspisR1.R22RawQmProductResidues.M
abbrev Delta := AspisR1FinishDotDecodedProductTrace.Delta

def tupleToTowerQ (r : M × M × M × M) : AspisV8R17.QM31WordTower.Q :=
  AspisV8R17.QM31WordTower.embedQ ((r.1,r.2.1),(r.2.2.1,r.2.2.2))

def decodeDelta (d : Delta) : AspisWideTower.WideExact :=
  ⟨tupleToTowerQ d.1, tupleToTowerQ d.2⟩

/-- The source finish output decodes to the two accumulated four-coordinate
residue tuples. The only arithmetic premise used upstream is the already
checked raw-residue trace in `successful_current_finish_query_product_words`.
-/
theorem successful_finish_decodes_accumulated_residues {W : Type}
    (ops : AspisR1FinishRelationCurrent.FinishOps W PushState)
    (fm : Slice U8) (ws : Slice FinishQM) (out : FinishE)
    (hrun : verifier.finish_query_dot
      (withConcreteDot (AspisR1CurrentWide.Proof.finishConcreteField ops)
        AspisR1EbyKPushDecodedProductUpdate.QRaw) fm ws = .ok (.Ok out)) :
    ∃ final : PushState, ∃ xs : List (Usize × FinishE × FinishQM),
      AspisR1FinishDotSourceABI.finishFromPush final = .ok out ∧
      AspisR1CurrentWide.Proof.decodeFinish out = decodeDelta (deltaSum xs) := by
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
        have hword := hwords
        rw [hshape0,hshape1] at hword
        have hvals := congrArg (List.map (fun w : U32 => w.val)) hword
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
        rw [hdelta] at hfinal
        exact ⟨final',xs,hfinish,hfinal⟩

#print axioms successful_finish_decodes_accumulated_residues
end AspisR1FinishDotReturnedDeltaDecodeV1
