import R1Z.ProverRwQueryStop
import R1Z.ProverRwQueryWindowStop
set_option autoImplicit false
namespace R1Z.ProverRwQueryBlock
open Aeneas Aeneas.Std Result ProverRwFull ProverRwQueryScan
open ProverRwQuerySourceWindow ProverRwQueryWindow ProverRwQueryStop
open Query31ExplicitScanBody
open Query31ExplicitListLoop (validState)
open Query31ConcreteWordsDriverChain Query31ModelScanCall

set_option backward.isDefEq.respectTransparency false in
theorem model_window (blocks : Blocks) (k : Nat) (hk : k<8) (s : CurrentScan)
    (hlen : s.accepted_len.val≤22) (bound : s.draws.val+8≤64) :
    modelScanFn actualQueryWords s (blocks.val[k]'(by simpa [blocks.property] using hk)) =
      window (blockWord blocks k hk) 8 0 s := by
  obtain ⟨words,hw⟩ := ProverCommitQueryTotal26.words_total
    (blocks.val[k]'(by simpa [blocks.property] using hk))
  have hv := AspisR1QueryScanUnrolled.r0_transcript.query_words_success_byte_mask _ words hw
  simp only [modelScanFn,hw,bind_tc_ok,hv]
  have h := list_window (blockWord blocks k hk) 8 0 s hlen bound
  have hrange : List.range' 0 8=List.range 8 := by decide
  rw [←h]
  simp only [hrange]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro p hp
  rcases p with ⟨sf,pending⟩
  rfl

theorem block_source (blocks advances : Blocks) (ki : Usize) (s : CurrentScan)
    (hk : ki.val<8) (hd : s.draws.val=8*ki.val) (hlen : s.accepted_len.val≤22) :
    ∃ stop sf,
      modelScanFn actualQueryWords s
        (blocks.val[ki.val]'(by simpa [blocks.property] using hk))=ok (stop,sf) ∧
      validState sf ∧
      run blocks advances s=(if stop then finishAt advances ki sf else run blocks advances sf) ∧
      (stop=false → sf.draws.val=8*(ki.val+1)) := by
  obtain ⟨stop,sf,hr,hvalid,ht,hf,hl,hu⟩ := window_total (blockWord blocks ki.val hk) 8 0 s hlen (by omega)
  have hm := model_window blocks ki.val hk s hlen (by omega)
  rw [hr] at hm
  have hs := window_source blocks advances ki.val 8 0 s hk (by omega) (by omega) hlen
  rw [hr,bind_tc_ok] at hs
  refine ⟨stop,sf,hm,hvalid,?_,by intro hh; have ht:=hf hh; omega⟩
  cases stop with
  | false => exact hs
  | true =>
    have strict := ProverRwQueryWindowStop.stop_lt (blockWord blocks ki.val hk) 8 0 s sf hlen (by omega) hr
    have index : min 7 (sf.draws.val/8)=ki.val := by omega
    exact hs.trans (run_at blocks advances ki sf (ht rfl) hvalid.2.1 hk index)

#print axioms model_window
#print axioms block_source
end R1Z.ProverRwQueryBlock
