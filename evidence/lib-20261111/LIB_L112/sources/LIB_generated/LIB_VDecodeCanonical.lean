import LIB_VArray
import NGO_CanonicalPort
set_option autoImplicit false
noncomputable section
namespace LIB_VDecodeCanonical
open Aeneas Aeneas.Std LIB_VScalarCarriers
open AspisR1 AspisR1PublicPreparation.RawActualDecodeKMainAdapter
abbrev Q := AspisR1DecodeKFullV10.aspis_core.field.QM31
def Canon (q : Q) : Prop := CanonicalRaw (decoderQMToMain q)
def All {N : Usize} (a : Array Q N) : Prop :=
 ∀ (i : Nat) (hi : i<a.val.length),Canon a.val[i]
theorem limbs (l : RetainedFieldByteCodec.QM31Limbs) :
 Canon (ActualDecodeKStrictQM31Parser.limbsToActual l) := by
 change ((M31ParserRefinement.valueToU32 (l 0)).val<2147483647 ∧
  (M31ParserRefinement.valueToU32 (l 1)).val<2147483647) ∧
  ((M31ParserRefinement.valueToU32 (l 2)).val<2147483647 ∧
  (M31ParserRefinement.valueToU32 (l 3)).val<2147483647)
 simp only [M31ParserRefinement.valueToU32_val]
 exact ⟨⟨(l 0).isLt,(l 1).isLt⟩,⟨(l 2).isLt,(l 3).isLt⟩⟩
theorem answer {N : Usize} {r : NGD_DecodeTrace.Record} {off start : Usize}
 (d : NGD_DecodeTrace.Domain N r off start) (i : Usize) (hi : i.val<N.val)
 (q : Q) (h : NGD_DecodeTrace.answer d i hi = .Ok q) : Canon q := by
 unfold NGD_DecodeTrace.answer NGD_DecodeValueLaw.expected at h
 cases hp : RetainedFieldByteCodec.decodeQM31LE
  (CandidateParserByteOrder.arrayBytes16 (NGD_DecodeValueLaw.input r off N i
   d.minlen d.cap d.positive hi d.range)) with
 | none => simp only [hp,Option.map_none] at h;cases h
 | some l =>
  simp only [hp,Option.map_some] at h
  have same : ActualDecodeKStrictQM31Parser.limbsToActual l=q := core.result.Result.Ok.inj h
  exact same ▸ limbs l

theorem trace {N : Usize} {r : NGD_DecodeTrace.Record} {off start : Usize}
 (d : NGD_DecodeTrace.Domain N r off start) (iter : NGD_DecodeTrace.Range)
 (out : Array Q N) (final : NGD_DecodeTrace.Final N)
 (t : NGD_DecodeTrace.Trace d iter out final) : All out → All final.1 := by
 induction t with
 | done iter out next => exact fun h=>h
 | reject iter nextIter index out live next error reply => exact fun h=>h
 | write iter nextIter index out updated live next q reply store final rest ih =>
  intro before
  apply ih
  intro j hj
  rw [NGO_DecodeFrame.store_value out updated index q live store]
  simp only [Array.set_val_eq,List.getElem_set]
  split
  · exact answer d index live q reply
  · exact before j (by simpa only [updated.property,out.property] using hj)
theorem zero (N : Usize) : All (Array.repeat N AspisR1DecodeKFullV10.aspis_core.field.QM31.ZERO) := by
 intro i hi
 simp only [Array.repeat_val,List.getElem_replicate]
 change (0<2147483647 ∧ 0<2147483647) ∧ (0<2147483647 ∧ 0<2147483647)
 exact ⟨⟨by omega,by omega⟩,⟨by omega,by omega⟩⟩
theorem array (N : Usize) (a : Array Q N) (h : All a) :
 LIB_VArray.Canonical (decoderArrayToMain a) := by
 intro q mem
 obtain ⟨x,hx,rfl⟩ := List.mem_map.mp mem
 obtain ⟨i,hi,same⟩ := List.mem_iff_getElem.mp hx
 rw [←same]
 exact h i hi
#print axioms limbs
#print axioms answer
#print axioms trace
#print axioms zero
#print axioms array
end LIB_VDecodeCanonical
