import Op4P_Accepted
import Op3I_Witness
import RowShape_SlotObstruction
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.Op4P_Audit
open AspisR1CurrentCaller MultiproofConeCanonical OraclePortCompactDraft
attribute [local instance] Classical.propDecidable

/-- The same existing D188 association remains constructively inhabited for
arbitrary unmodified slots. No native acceptance premise is certified here. -/
theorem extraction_satisfiable (adapterOps : AdapterRw.Ops) (ops : Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest) :
    ∃ native1 native2,
      S2W_DigestExtraction.AeneasExtraction
        (ClaimsUnrolledSdk.sdkOps
          {adapterOps with op43 := S2W_DigestExtraction.digest hashv}
          (Op3I_Install.install (Op4P_Install.install ops)) B std)
        native1 native2 hashv :=
  Op3I_Nonvacuity.extraction_satisfiable adapterOps (Op4P_Install.install ops) B std hashv

theorem little_zeros (n : Nat) :
    little (List.replicate n (0 : AspisV8R19.DuplexFrames.Byte)) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ,little,List.foldr_cons] at *; rw [ih]; rfl

theorem canonical_zeros (n : Nat) (aligned : n % 4 = 0) :
    canonical (List.replicate n (0 : AspisV8R19.DuplexFrames.Byte)) := by
  refine ⟨by simpa only [List.length_replicate] using aligned,?_⟩
  intro j _
  simp only [slice,List.drop_replicate,List.take_replicate,little_zeros]
  decide

theorem witness_zero_slice (offset size : Nat) (lo : 9 ≤ offset) (hi : offset+size ≤ 57607) :
    slice (bytesOf Op3I_Witness.proof.val) offset size = List.replicate size 0 := by
  simp only [slice,bytesOf,Op3I_Witness.proof,List.map_append,List.map_replicate,
    List.drop_append,List.length_map]
  have prefixLength : Op3I_Witness.headerBytes.length = 9 := rfl
  have dropPrefix : (Op3I_Witness.headerBytes.map fun x =>
      (⟨x.val,by scalar_tac⟩ : AspisV8R19.DuplexFrames.Byte)).drop offset = [] :=
    List.drop_eq_nil_of_le (by simp only [List.length_map,prefixLength]; exact lo)
  rw [dropPrefix,List.nil_append,prefixLength]
  simp only [List.drop_replicate,List.take_replicate]
  congr 1
  omega

/-- Existing symbolic header fixture also succeeds in the newly installed scan.
This proves local joint header/scan non-vacuity, not spend acceptance. -/
theorem witness_scan : scan (bytesOf Op3I_Witness.proof.val) := by
  refine ⟨?_,?_,?_,?_⟩
  · rw [witness_zero_slice 7031 464 (by decide) (by decide)]
    exact canonical_zeros _ (by decide)
  · rw [witness_zero_slice 7495 256 (by decide) (by decide)]
    exact canonical_zeros _ (by decide)
  · rw [witness_zero_slice 7783 2272 (by decide) (by decide)]
    exact canonical_zeros _ (by decide)
  · intro j hj
    have bound := List.mem_range.mp hj
    rw [witness_zero_slice (10055+j*832) 832 (by omega) (by omega)]
    constructor
    · rw [List.take_replicate]
      exact canonical_zeros 608 (by decide)
    · simp only [slice,List.drop_replicate,List.take_replicate]
      exact canonical_zeros 128 (by decide)

theorem witness_success :
    Op3I_Install.sourceBody Op3I_Witness.proof = ok (.Ok .S2) ∧
    Op4P_Install.sourceBody Op3I_Witness.proof = ok (.Ok ()) := by
  refine ⟨Op3I_Witness.source_success,?_⟩
  simp only [Op4P_Install.sourceBody,
    Op4P_Refinement.reference_total _ Op3I_Witness.fields.1,witness_scan,if_true,bind_tc_ok]

/-- The original permissive-slot padding witness cannot return success. -/
theorem rejects_padding :
    Op4P_Install.sourceBody RowShape_SlotObstruction.badScan = ok (.Err .Parse) := by
  have len : Slice.len RowShape_SlotObstruction.badScan = 7035#usize := by
    apply UScalar.eq_of_val_eq
    simp only [RowShape_SlotObstruction.badScan,List.length_append,List.length_replicate,
      List.length_cons,List.length_nil]
  simp only [Op4P_Install.sourceBody,Op4P_Extract.Op4P_reference.canonical_scan,
    Op4P_Refinement.scanner_emission,MultiproofParserRef.parser_reference.scan,
    len,show (7035#usize != 57607#usize) = true by decide,if_true,bind_tc_ok,
    Bool.false_eq_true,if_false]

/-- Put the same noncanonical first word at the deployed length, so length
admission cannot explain rejection of this stronger witness. -/
def padded : Slice U8 :=
  ⟨RowShape_SlotObstruction.badScan.val ++ List.replicate 50572 0#u8, by
    simp only [RowShape_SlotObstruction.badScan,List.length_append,List.length_replicate,
      List.length_cons,List.length_nil]
    scalar_tac⟩

theorem padded_length : padded.val.length = 57607 := by
  simp only [padded,RowShape_SlotObstruction.badScan,List.length_append,List.length_replicate,
    List.length_cons,List.length_nil]

theorem padded_bad : ¬ scan (bytesOf padded.val) := by
  intro good
  have word := good.1.2 0 (by
    simp only [slice,bytesOf,padded,RowShape_SlotObstruction.badScan,List.length_map,
      List.length_take,List.length_drop,List.length_append,List.length_replicate,
      List.length_cons,List.length_nil,List.mem_range]
    decide)
  have segment : slice (slice (bytesOf padded.val) 7031 464) (4*0) 4 = [255,255,255,255] := by
    simp only [slice,bytesOf,padded,RowShape_SlotObstruction.badScan,List.map_append,
      List.map_replicate,List.map_cons,List.map_nil,List.drop_append,List.length_replicate,
      List.drop_replicate,Nat.sub_self,List.replicate_zero,List.nil_append,
      List.drop_zero,Nat.mul_zero,List.take_take]
    rfl
  rw [segment] at word
  norm_num [little] at word

theorem rejects_padded : Op4P_Install.sourceBody padded ≠ ok (.Ok ()) := by
  intro success
  exact padded_bad (Op4P_Install.scan_of_success padded padded_length success)

#print axioms extraction_satisfiable
#print axioms little_zeros
#print axioms canonical_zeros
#print axioms witness_zero_slice
#print axioms witness_scan
#print axioms witness_success
#print axioms rejects_padding
#print axioms padded_length
#print axioms padded_bad
#print axioms rejects_padded
end AspisR1.Op4P_Audit
end
