import NKL_CanonicalK
import NKB_CanonicalScalarBridge
set_option autoImplicit false
noncomputable section
namespace NKL_WordCanonical
open Aeneas Aeneas.Std Result AspisR1
open OraclePortCompactDraft MultiproofConeCanonical
open RetainedFieldByteCodec CheckpointBytes3KDecode CheckpointBytes3ScalarShape OraclePortCkptAbi4Decode
attribute [local instance] Classical.propDecidable

theorem one (bs : AspisV8R19.DuplexFrames.Bytes) (width:bs.length=4) :
 canonical bs ↔ little bs<2147483647 := by
 have take : bs.take 4=bs := by rw [←width,List.take_length]
 simp [canonical,width,slice,take]

theorem scalar_bytes (b : Array U8 4#usize) :
 List.ofFn (M31ParserArray.arrayBytes b)=bytesOf b.val := by
 apply List.ext_getElem
 · simp only [List.length_ofFn,bytesOf,List.length_map]
   exact b.property.symm
 · intro i left right
   simp only [List.getElem_ofFn,bytesOf,List.getElem_map,M31ParserArray.arrayBytes]

theorem scalar (b : Array U8 4#usize) :
 NKB_CanonicalScalarBridge.good b=true ↔ canonical (bytesOf b.val) := by
 unfold NKB_CanonicalScalarBridge.good
 rw [decide_eq_true_eq,one (bytesOf b.val) (by simp only [bytesOf,List.length_map];exact b.property)]
 have h:=MultiproofConeEndian.strict_word_iff b
 rw [←MultiproofConeEndian.little_four,scalar_bytes] at h
 exact h

theorem limb_bytes (b : Array U8 16#usize) (j : Fin 4) :
 List.ofFn (qm31LimbBytes (fixed b.to_slice b.property) j)=
 bytesOf ((b.val.drop (4*j.val)).take 4) := by
 have width : b.val.length=16 := b.property
 apply List.ext_getElem
 · simp only [List.length_ofFn,bytesOf,List.length_map,List.length_take,List.length_drop]
   omega
 · intro n left right
   simp only [List.getElem_ofFn,bytesOf,List.getElem_map,List.getElem_take,List.getElem_drop,
     qm31LimbBytes,fixed,limbByteIndex_val,Fin.val_mk,Array.to_slice]
   congr 1
   simp only [Nat.add_comm]

theorem k_word (b : Array U8 16#usize) (j : Fin 4) :
 (word b.to_slice b.property j).val=
 little (slice (bytesOf b.val) (4*j.val) 4) := by
 rw [word_model,←MultiproofConeEndian.little_four,limb_bytes]
 rfl

theorem k (b : Array U8 16#usize) :
 NKB_CanonicalKBridge.good b=true ↔ canonical (bytesOf b.val) := by
 have width : b.val.length=16 := b.property
 unfold NKB_CanonicalKBridge.good
 simp only [decide_eq_true_eq,Canonical,kWords]
 have right : canonical (bytesOf b.val) ↔
   ∀ j : Fin 4,(word b.to_slice b.property j).val<2147483647 := by
  simp only [canonical,bytesOf,List.length_map,width]
  change (0=0 ∧ ∀ n∈List.range 4,
    little (slice (bytesOf b.val) (4*n) 4)<2147483647) ↔ _
  simp only [true_and,List.mem_range]
  constructor
  · intro all j
    rw [k_word]
    exact all j.val j.isLt
  · intro all n bound
    have h:=all ⟨n,bound⟩
    rw [k_word] at h
    exact h
 rw [right]
 constructor
 · intro all j
   fin_cases j
   · exact all.1
   · exact all.2.1
   · exact all.2.2.1
   · exact all.2.2.2
 · intro all
   exact ⟨all 0,all 1,all 2,all 3⟩

#print axioms one
#print axioms scalar_bytes
#print axioms scalar
#print axioms limb_bytes
#print axioms k_word
#print axioms k
end NKL_WordCanonical
end
