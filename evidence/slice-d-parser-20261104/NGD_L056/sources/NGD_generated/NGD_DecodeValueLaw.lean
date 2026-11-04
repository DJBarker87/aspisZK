import NGD_DecodeValueTotal
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace NGD_DecodeValueLaw
open AspisR1DecodeKFullV10

noncomputable def input (r : r1_wire.ValidatedRecord) (off n index : Usize)
    (minlen : 5≤r.framed.val.length) (cap : r.framed.val.length≤3717)
    (positive : 0<n.val) (live : index.val<n.val)
    (range : 32*off.val+32*n.val≤r.framed.val.length-5) : Array U8 16#usize :=
  ⟨((r.framed.val.drop 5).drop (32*(off.val+index.val))).take 16,by
    have g := NGD_DecodeGeometry.fitting r.framed.val.length off.val n.val index.val minlen cap positive live range
    simp only [List.length_take,List.length_drop]
    change min 16 (r.framed.val.length-5-32*(off.val+index.val))=16
    omega⟩

noncomputable def errorIndex (r : r1_wire.ValidatedRecord) (off n index : Usize)
    (minlen : 5≤r.framed.val.length) (cap : r.framed.val.length≤3717)
    (positive : 0<n.val) (live : index.val<n.val)
    (range : 32*off.val+32*n.val≤r.framed.val.length-5) : Usize :=
  UScalar.ofNat (off.val+index.val) (by
    have g := NGD_DecodeGeometry.fitting r.framed.val.length off.val n.val index.val minlen cap positive live range
    scalar_tac)

noncomputable def expected (r : r1_wire.ValidatedRecord) (off n index : Usize)
    (minlen : 5≤r.framed.val.length) (cap : r.framed.val.length≤3717)
    (positive : 0<n.val) (live : index.val<n.val)
    (range : 32*off.val+32*n.val≤r.framed.val.length-5) :
    core.result.Result aspis_core.field.QM31 r1_wire.Error :=
  match (AspisR1.RetainedFieldByteCodec.decodeQM31LE
    (AspisR1.CandidateParserByteOrder.arrayBytes16 (input r off n index minlen cap positive live range))).map
      AspisR1.ActualDecodeKStrictQM31Parser.limbsToActual with
  | none => .Err (.NonCanonical r.row (errorIndex r off n index minlen cap positive live range))
  | some q => .Ok q

/-- Full emitted one-value result on the SAME original input window. -/
theorem value (r : r1_wire.ValidatedRecord) (off byteOffset n index : Usize)
    (minlen : 5≤r.framed.val.length) (cap : r.framed.val.length≤3717)
    (byteStart : byteOffset.val=32*off.val) (positive : 0<n.val) (live : index.val<n.val)
    (range : 32*off.val+32*n.val≤r.framed.val.length-5) :
    r1_wire.ValidatedRecord.decode_k_value r byteOffset index off =
      ok (expected r off n index minlen cap positive live range) := by
  have geometry := NGD_DecodeGeometry.fitting r.framed.val.length off.val n.val index.val minlen cap positive live range
  have spec : r1_wire.ValidatedRecord.decode_k_value r byteOffset index off ⦃ out =>
      out=expected r off n index minlen cap positive live range ⦄ := by
    unfold r1_wire.ValidatedRecord.decode_k_value
    step*
    simp only [s_post]
    let assembled : Array U8 16#usize := Array.make 16#usize
      [i1,i3,i5,i7,i9,i11,i13,i15,i17,i19,i21,i23,i25,i27,i29,i31]
    have same : assembled = input r off n index minlen cap positive live range := by
      apply Subtype.ext
      apply List.ext_getElem
      · simp only [assembled,Array.make,input,List.length_take,List.length_drop]
        omega
      · intro j hj hk
        have small : j<16 := by simpa only [assembled,Array.make] using hj
        interval_cases j <;> simp_all [assembled,Array.make,input,Nat.mul_add,Nat.mul_comm,Nat.add_assoc] <;> congr 1 <;> omega
    change (do
      let o ← aspis_core.field.QM31.from_le_bytes (Array.to_slice assembled)
      let i32 ← off + index
      core.option.Option.ok_or o (r1_wire.Error.NonCanonical r.row i32)) ⦃ out =>
        out=expected r off n index minlen cap positive live range ⦄
    rw [same]
    step*
    have lastEq : i32 = errorIndex r off n index minlen cap positive live range := by
      apply UScalar.eq_of_val_eq
      simpa only [errorIndex] using i32_post
    simp [core.option.Option.ok_or,o_post,lastEq,expected]
  obtain ⟨out,call,eq⟩ := WP.spec_imp_exists spec
  exact call.trans (congrArg ok eq)
#print axioms value
end NGD_DecodeValueLaw
