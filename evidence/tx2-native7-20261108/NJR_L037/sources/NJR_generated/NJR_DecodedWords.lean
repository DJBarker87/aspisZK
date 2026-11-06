import NJR_HistoryFromScan
import NJC_EReaderResults
set_option autoImplicit false
noncomputable section
namespace NJR_DecodedWords
open Aeneas Aeneas.Std Result AspisR1
open OraclePortCkptAbi4Decode CheckpointBytes3EShape CheckpointBytes3EDecode
open MultiproofConeCanonical OraclePortCompactDraft

theorem decoded (b : Array U8 32#usize) (x : AspisWideTower.WideExact)
 (run : FoldedLeafCodec.decodeWide (bytesOf b.val)=some x) (j : Fin 8) :
 NIG_FinishInput.word b.val (4*j.val)<2147483647 := by
 have result:=NJC_EReaderResults.decodeE b
 have actual : FoldedLeafCodec.decodeWide (bytesOf b.to_slice.val)=some x := run
 rw [decode_e_identification b.to_slice b.property] at result
 rw [actual] at result
 simp only [Option.map_some,bind_tc_ok,CheckpointBytes3Reader.optionE] at result
 have canonical : CanonicalWide (eWords (word32 b.to_slice b.property)) := by
  by_contra bad
  dsimp only [NJC_EReaderResults.naturalE] at result
  rw [if_neg bad] at result
  cases result
 have bound : (word32 b.to_slice b.property j).val<2147483647 := by
  fin_cases j
  all_goals first
  | exact canonical.1.1
  | exact canonical.1.2.1
  | exact canonical.1.2.2.1
  | exact canonical.1.2.2.2
  | exact canonical.2.1
  | exact canonical.2.2.1
  | exact canonical.2.2.2.1
  | exact canonical.2.2.2.2
 have size : b.val.length=32 := b.property
 have h0 : 4*j.val<b.val.length := by omega
 have h1 : 4*j.val+1<b.val.length := by omega
 have h2 : 4*j.val+2<b.val.length := by omega
 have h3 : 4*j.val+3<b.val.length := by omega
 simpa only [word32,CheckpointBytes3Word.pack_value,NIG_FinishInput.word,
  List.getElem?_eq_getElem h0,List.getElem?_eq_getElem h1,
  List.getElem?_eq_getElem h2,List.getElem?_eq_getElem h3,Option.getD_some] using bound

/-- A successful strict decoder at an actual bounded window yields all eight
raw natural word bounds. No encoded-field or canonical-input premise. -/
theorem window (bytes : Slice U8) (offset : Nat) (fits : offset+32≤bytes.val.length)
 (x : AspisWideTower.WideExact)
 (run : FoldedLeafCodec.decodeWide (slice (bytesOf bytes.val) offset 32)=some x)
 (j : Fin 8) : NIG_FinishInput.word bytes.val (offset+4*j.val)<2147483647 := by
 let b : Array U8 32#usize:=⟨(bytes.val.drop offset).take 32,by
  simp only [List.length_take,List.length_drop];change _=32;omega⟩
 have actual : FoldedLeafCodec.decodeWide (bytesOf b.val)=some x := by
  simpa only [b,bytesOf,slice,List.map_take,List.map_drop] using run
 have bound:=decoded b x actual j
 change NIG_FinishInput.word ((bytes.val.drop offset).take 32) (4*j.val)<2147483647 at bound
 rw [NJR_FinishWindows.word_window _ offset 32 (4*j.val) (by omega)] at bound
 exact bound

#print axioms decoded
#print axioms window
end NJR_DecodedWords
