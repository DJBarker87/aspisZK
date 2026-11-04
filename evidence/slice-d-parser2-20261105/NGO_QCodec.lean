import NGO_QResult
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGO_QCodec
open NGO_QAssociation NGO_QResult AspisR1.RetainedFieldByteCodec
noncomputable def limbsToRef (limbs : QM31Limbs) : NGO_QRef.QM31 :=
  ⟨⟨AspisR1.M31ParserRefinement.valueToU32 (limbs 0),
     AspisR1.M31ParserRefinement.valueToU32 (limbs 1)⟩,
   ⟨AspisR1.M31ParserRefinement.valueToU32 (limbs 2),
     AspisR1.M31ParserRefinement.valueToU32 (limbs 3)⟩⟩
theorem specification_codec (arr : Array U8 16#usize) :
    specification arr =
      (decodeQM31LE (AspisR1.CandidateParserByteOrder.arrayBytes16 arr)).map limbsToRef := by
  let bytes := AspisR1.CandidateParserByteOrder.arrayBytes16 arr
  by_cases canonical : ∀ i : Fin 4, (word arr i).val<2147483647
  · have codecCanonical : ∀ i : Fin 4, (decodeWordLE (qm31LimbBytes bytes i)).val<m31Modulus := by
      intro i
      have h := canonical i
      rw [word_value] at h
      exact h
    have good0 : ¬word arr 0>=2147483647#u32 := by change ¬2147483647≤(word arr 0).val;have h:=canonical 0;omega
    have good1 : ¬word arr 1>=2147483647#u32 := by change ¬2147483647≤(word arr 1).val;have h:=canonical 1;omega
    have good2 : ¬word arr 2>=2147483647#u32 := by change ¬2147483647≤(word arr 2).val;have h:=canonical 2;omega
    have good3 : ¬word arr 3>=2147483647#u32 := by change ¬2147483647≤(word arr 3).val;have h:=canonical 3;omega
    simp only [specification,if_neg good0,if_neg good1,if_neg good2,if_neg good3]
    change _=(decodeQM31LE bytes).map limbsToRef
    unfold decodeQM31LE
    rw [dif_pos codecCanonical]
    simp only [Option.map_some,Option.some.injEq,limbsToRef]
    congr 1 <;> congr 1 <;> apply UScalar.eq_of_val_eq <;>
      simp only [AspisR1.M31ParserRefinement.valueToU32_val] <;> exact word_value arr _
  · obtain ⟨i,bad⟩ := not_forall.mp canonical
    have notCodec : ¬∀ j, (decodeWordLE (qm31LimbBytes bytes j)).val<m31Modulus := by
      intro all
      have h:=all i
      have eq:=word_value arr i
      exact bad (by change (word arr i).val<2147483647;change (decodeWordLE (qm31LimbBytes bytes i)).val<2147483647 at h;omega)
    have strict : decodeQM31LE bytes=none := by unfold decodeQM31LE;rw [dif_neg notCodec]
    change _=(decodeQM31LE bytes).map limbsToRef
    rw [strict]
    have noncanonical : word arr i>=2147483647#u32 := by change 2147483647≤(word arr i).val;omega
    fin_cases i <;> simp_all [specification]
#print axioms specification_codec
end NGO_QCodec
