import FIr_LiteralRow
import R3SemanticRemainingJoins
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIr_LiteralValues
open R0P.Mask
open LiteralSemanticCodecBridge
abbrev E := LiteralSemanticPrefix.E

theorem claim (values : SemanticPrefixCodec.Full)
    (rs : List (Message × Challenge)) (view : LiteralOpeningView.View)
    (read : LiteralOpeningView.read rs=some view)
    (frames : SemanticPrefixCodec.encodeFull values=records (rs.take 25)) :
    claimOf (SelectedSemanticPrefixFacts.lift view.semantic)=some (SemanticPayloadView.claimAt14 values) := by
  obtain ⟨length,_,_,semantic,_⟩ := LiteralOpeningPrefixFacts.read_prefix_components rs view read
  obtain ⟨c,slot⟩ := FIr_LiteralRow.parsed_row _ values (rs.take 25) view.semantic semantic frames length (14:Fin 25)
  change view.semantic[14]'(by rw [view.semantic_length];decide) = (SemanticPayloadView.toMessage _ (values ⟨14,by decide⟩).val,c) at slot
  rw [SemanticPayloadView.toMessage_claimAt14] at slot
  unfold claimOf SelectedSemanticPrefixFacts.lift
  rw [List.getElem?_map,List.getElem?_eq_getElem (by rw [view.semantic_length];decide)]
  simp only [slot,Option.map_some]

theorem polynomials (values : SemanticPrefixCodec.Full)
    (rs : List (Message × Challenge)) (view : LiteralOpeningView.View)
    (read : LiteralOpeningView.read rs=some view)
    (frames : SemanticPrefixCodec.encodeFull values=records (rs.take 25)) :
    semPolysZ (SelectedSemanticPrefixFacts.lift view.semantic)=
      some (fun j => SemanticCoefficientCodec.polynomial (SemanticPayloadView.coeffAt values j)) := by
  classical
  obtain ⟨length,_,_,semantic,_⟩ := LiteralOpeningPrefixFacts.read_prefix_components rs view read
  have slot (j : Fin 10) :
      ((SelectedSemanticPrefixFacts.lift view.semantic)[15+j.val]'(by
        simp only [SelectedSemanticPrefixFacts.lift,List.length_map,view.semantic_length];omega)).1=
      R0C.SemStatement.Msg.semantic (.base (.roundPoly
        (SemanticCoefficientCodec.polynomial (SemanticPayloadView.coeffAt values j)))) := by
    obtain ⟨c,eq⟩ := FIr_LiteralRow.parsed_row _ values (rs.take 25) view.semantic semantic frames length
      ⟨15+j.val,by omega⟩
    rw [SemanticPayloadView.toMessage_coeffAt] at eq
    simp only [SelectedSemanticPrefixFacts.lift,List.getElem_map,eq]
  have len : (SelectedSemanticPrefixFacts.lift view.semantic).length=25 := by
    simp only [SelectedSemanticPrefixFacts.lift,List.length_map,view.semantic_length]
  simp only [semPolysZ,dif_pos len,slot,Option.isSome_some,Option.get_some]
  rfl

#print axioms claim
#print axioms polynomials
end AspisR1.FIr_LiteralValues
end
