import RPz7_S1QueryWordModelV1
import R0C.V3.Q22Law
import S1QueryArrayOperationsV1
set_option autoImplicit false
noncomputable section
namespace AspisS1QueryScanModel
open Aeneas Aeneas.Std Result
open AspisV8R19.SqueezeOracleBridge AspisV8R19.SourceDuplexStep
open AspisV8R19.Q22WordScan
open Query31ExplicitScanBody Query31ExplicitListLoop Query31ModelScanCall
open Query31ConcreteWordsDriverChain AspisS1QueryWordModel
abbrev Bytes32 := Array U8 32#usize
abbrev Blocks8 := Array Bytes32 8#usize
abbrev QueryScan := Query31ModelDriverChain.QueryScan

/-- TOTAL mathematical draw bound, including early-stop paths. -/
theorem scan_draw_le (s : ScanState) (xs : List Nat) :
    (scan s xs).1.draws ≤ s.draws+xs.length := by
  induction xs generalizing s with
  | nil => simp only [scan,List.length_nil,Nat.add_zero]; exact Nat.le_refl _
  | cons x xs ih =>
    simp only [scan]
    split
    · simp only [List.length_cons]; omega
    · have h := ih ⟨keep s.accepted x,s.draws+1⟩
      dsimp only at h
      simp only [List.length_cons]
      omega

/-- Same returned state/stop bit for the exact source-shaped word decoder. -/
theorem source_scan_math (s sf : QueryScan) (block : Bytes32) (stop : Bool)
    (valid : validState s)
    (success : modelScanFn actualQueryWords s block=ok (stop,sf)) :
    scan (q22StateOf s) (AspisV8R19.SamplerWords.words 18 (decodeState block))=
      (q22StateOf sf,stop) ∧ validState sf := by
  obtain ⟨words,decoded,scanned,validFinal⟩ :=
    modelScanFn_success actualQueryWords s sf block stop valid success
  rw [query_words_math block words decoded] at scanned
  exact ⟨scanned,validFinal⟩

/-- Source success identifies the complete accepted buffer, not merely its set. -/
theorem source_finish_math (s : QueryScan) (accepted : Array U32 22#usize)
    (success : AspisR1Query31Transcript.aspis_core.r0_transcript.QueryScan.finish s=
      ok (.Ok accepted)) :
    finish (q22StateOf s)=.ok (accepted.val.map (fun w => w.val)) := by
  obtain ⟨length,buffer⟩ := (AspisR1Query31Transcript.finish_success_iff s accepted).mp success
  have hlen : s.accepted_len.val=22 := by
    rw [length]
    simp only [AspisR1Query31Transcript.aspis_core.r0_transcript.QUERY_COUNT]
    rfl
  have alen : accepted.val.length=22 := accepted.property
  simp [finish,q22StateOf,acceptedPrefix,hlen,← buffer,alen]

/-- Every source-selected block is the corresponding element of the SAME
mathematical array suffix. The bound is discharged at concrete driver indices. -/
def statesFrom (a : Blocks8) (i : Nat) : List State := (a.val.drop i).map decodeState

theorem statesFrom_cons (a : Blocks8) (i : Usize) (bound : i.val<8)
    (value : Bytes32) (selected : Array.index_usize a i=ok value) :
    statesFrom a i.val=decodeState value :: statesFrom a (i.val+1) := by
  have length : a.val.length=8 := a.property
  have index := AspisS1QueryArrayOperations.index_total a i bound
  rw [selected] at index
  have eq := Result.ok.inj index
  unfold statesFrom
  rw [List.drop_eq_getElem_cons (by omega : i.val<a.val.length),List.map_cons]
  rw [eq]

theorem source_scan_draw_le (s sf : QueryScan) (block : Bytes32) (stop : Bool)
    (valid : validState s)
    (success : modelScanFn actualQueryWords s block=ok (stop,sf)) :
    sf.draws.val≤s.draws.val+8 := by
  have scanned := (source_scan_math s sf block stop valid success).1
  have bound := scan_draw_le (q22StateOf s)
    (AspisV8R19.SamplerWords.words 18 (decodeState block))
  rw [scanned] at bound
  simpa only [q22StateOf,AspisV8R19.SamplerWords.words_length] using bound

def blockAt (a : Blocks8) (i : Usize) (bound : i.val<8) : Bytes32 :=
  a.val[i.val]'(by have length : a.val.length=8 := a.property; omega)

theorem blockAt_selected (a : Blocks8) (i : Usize) (bound : i.val<8) :
    Array.index_usize a i=ok (blockAt a i bound) :=
  AspisS1QueryArrayOperations.index_total a i bound

/-- One actual scanner call advances the fixed model over the same array
suffix. The model's outer draw guard is made explicit, never assumed away. -/
theorem scanOut_source_step (n : Nat) (s sf : QueryScan) (blocks advances : Blocks8)
    (i : Usize) (bound : i.val<8) (block : Bytes32) (stop : Bool) (state : State)
    (valid : validState s) (draws : s.draws.val<64)
    (selected : Array.index_usize blocks i=ok block)
    (success : modelScanFn actualQueryWords s block=ok (stop,sf)) :
    R0C.V3.Q22.scanOut (n+1) (q22StateOf s)
      (statesFrom blocks i.val) (statesFrom advances i.val) state=
      if stop then (finish (q22StateOf sf),decodeState (blockAt advances i bound))
      else R0C.V3.Q22.scanOut n (q22StateOf sf)
        (statesFrom blocks (i.val+1)) (statesFrom advances (i.val+1))
        (decodeState (blockAt advances i bound)) := by
  rw [statesFrom_cons blocks i bound block selected,
    statesFrom_cons advances i bound _ (blockAt_selected advances i bound)]
  have scanned := (source_scan_math s sf block stop valid success).1
  simp only [R0C.V3.Q22.scanOut,show (q22StateOf s).draws<64 from draws,
    if_true,scanned]

#print axioms source_scan_draw_le
#print axioms blockAt_selected
#print axioms scanOut_source_step
#print axioms scan_draw_le
#print axioms source_scan_math
#print axioms source_finish_math
#print axioms statesFrom_cons
end AspisS1QueryScanModel
