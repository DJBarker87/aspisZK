import S4CanonicalHeadWordRootV1
import MultiproofConeCanonicalAppend
import FourDotsCurrentQmParserRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FastDotsCanonicalQmWordRootV1
open AspisR1.MultiproofConeCanonical (bytesOf)
open AspisR1.OraclePortCompactDraft (canonical slice little)
open AspisR1.RetainedFieldByteCodec
open AspisR1.CandidateParserByteOrder (arrayBytes16)

theorem canonical_slice (xs : AspisV8R19.DuplexFrames.Bytes) (offset count : Nat)
    (hc : canonical xs) (ho : offset%4=0) (hn : count%4=0)
    (hb : offset+count≤xs.length) : canonical (slice xs offset count) := by
  have hd := (AspisR1.MultiproofConeCanonicalAppend.canonical_take_drop xs offset ho (by omega)).mp hc
  have ht := (AspisR1.MultiproofConeCanonicalAppend.canonical_take_drop (xs.drop offset) count hn
    (by simp only [List.length_drop]; omega)).mp hd.2
  exact ht.1

theorem limb_bytes_list (a : Array Std.U8 16#usize) (limb : Fin 4) :
    List.ofFn (qm31LimbBytes (arrayBytes16 a) limb)=
      slice (bytesOf a.val) (4*limb.val) 4 := by
  apply List.ext_getElem
  · simp only [List.length_ofFn,slice,bytesOf,List.length_take,List.length_drop,List.length_map,a.property]
    change 4=min 4 (16-4*limb.val)
    omega
  · intro i hi hj
    simp only [List.getElem_ofFn,slice,bytesOf,List.getElem_take,List.getElem_drop,List.getElem_map,
      qm31LimbBytes,arrayBytes16,limbByteIndex_val]
    congr 1
    omega

theorem canonical_qm_parser_forward (a : Array Std.U8 16#usize)
    (hc : canonical (bytesOf a.val)) :
    ∃ q : AspisR1FastDotsCurrentQmParserRootV1.QM,
      AspisR1FastDotsCurrentQmParserRootV1.parser (Array.to_slice a)=.ok (some q) := by
  have hall : ∀ limb : Fin 4,
      (decodeWordLE (qm31LimbBytes (arrayBytes16 a) limb)).val<m31Modulus := by
    intro limb
    rw [← AspisR1.MultiproofConeEndian.little_four,limb_bytes_list]
    apply hc.2 limb.val
    simp only [List.mem_range,bytesOf,List.length_map,a.property]
    exact limb.isLt
  let limbs : QM31Limbs := fun limb=>⟨decodeWordLE (qm31LimbBytes (arrayBytes16 a) limb),hall limb⟩
  refine ⟨AspisR1FastDotsCurrentQmParserRootV1.limbsToCurrent limbs,?_⟩
  rw [AspisR1FastDotsCurrentQmParserRootV1.parser_fixed_total]
  simp only [decodeQM31LE,dif_pos hall,Option.map_some]
#print axioms canonical_slice
#print axioms limb_bytes_list
#print axioms canonical_qm_parser_forward
end AspisR1FastDotsCanonicalQmWordRootV1
