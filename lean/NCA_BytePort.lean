import LPt_LPl_Check
import S8JoinFrozenScan
import NBR_ProducerBuffers
set_option autoImplicit false
namespace AspisR1.NCA_BytePort
open Aeneas Aeneas.Std
open OraclePortCompactDraft MultiproofConeCanonical

theorem little (bs : List U8) :
    OraclePortCompactDraft.little (bytesOf bs) = bs.foldr (fun b n => b.val+256*n) 0 := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [bytesOf,List.map_cons,OraclePortCompactDraft.little,List.foldr_cons] at *
    rw [ih]
    rfl

theorem window (bs : List U8) (start count : Nat) :
    bytesOf ((bs.drop start).take count)=slice (bytesOf bs) start count := by
  simp only [bytesOf,slice,List.map_take,List.map_drop]

theorem word (bs : List U8) :
    LPt_LPl_Kit_Bytes.le32 bs = OraclePortCompactDraft.little (bytesOf (bs.take 4)) := by
  rw [little]
  rfl

theorem canonical_chunk (bs : List U8) (size : bs.length=16)
    (canonical : OraclePortCompactDraft.canonical (bytesOf bs)) :
    LPt_LPl_Kit_Bytes.validChunk 4 false bs=true := by
  simp only [LPt_LPl_Kit_Bytes.validChunk,List.all_eq_true]
  intro j hj
  have bound : j<4 := List.mem_range.mp hj
  have h := canonical.2 j (List.mem_range.mpr (by simp only [bytesOf,List.length_map,size];omega))
  have same : LPt_LPl_Kit_Bytes.le32 ((bs.drop (4*j)).take 4) =
      OraclePortCompactDraft.little (slice (bytesOf bs) (4*j) 4) := by
    rw [word,List.take_take]
    simpa only [Nat.min_self] using congrArg OraclePortCompactDraft.little (window bs (4*j) 4)
  simp only [Bool.not_false,Bool.true_or,Bool.and_true,decide_eq_true_eq]
  rw [same]
  exact h

#print axioms little
#print axioms window
#print axioms word
#print axioms canonical_chunk
end AspisR1.NCA_BytePort
