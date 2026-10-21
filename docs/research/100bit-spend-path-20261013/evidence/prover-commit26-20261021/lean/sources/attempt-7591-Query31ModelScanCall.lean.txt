import Query31ExplicitListLoop

import Query31UnrolledDriverFirstStop
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false

namespace Query31ModelScanCall
open Query31ExplicitListLoop Query31ExplicitScanBody AspisV8R19.Q22WordScan
abbrev QueryScan := AspisR1Query31Transcript.aspis_core.r0_transcript.QueryScan

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = ok v) : ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

private theorem pair_bind_success {α β γ : Type} (m : Result (α × β))
    (k : α → β → Result γ) (v : γ)
    (h : (do let (a,b) ← m; k a b) = ok v) :
    ∃ a b, m = ok (a,b) ∧ k a b = ok v := by
  cases m with
  | ok pair => cases pair with | mk a b => exact ⟨a,b,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- The explicit source-shaped scan model. Byte-block decoding is kept as a
    caller-supplied operation; iterator semantics are the checked list model. -/
def modelScanFn
    (decodeBlock : Array Std.U8 32#usize → Result (Array Std.U32 8#usize))
    (s : QueryScan) (block : Array Std.U8 32#usize) :
    Result (Bool × QueryScan) := do
  let words ← decodeBlock block
  let (sf, pending) ← scanListLoop words.val s
  ok (optionStop pending, sf)

/-- A successful modeled block scan supplies its decoded words, the exact Q22
    transition for those words, and validity of the resulting scanner state. -/
theorem modelScanFn_success
    (decodeBlock : Array Std.U8 32#usize → Result (Array Std.U32 8#usize))
    (s sf : QueryScan) (block : Array Std.U8 32#usize) (stop : Bool)
    (hs : validState s)
    (hcall : modelScanFn decodeBlock s block = .ok (stop, sf)) :
    ∃ words : Array Std.U32 8#usize,
      decodeBlock block = .ok words ∧
      scan (q22StateOf s) (words.val.map (fun x => x.val)) =
        (q22StateOf sf, stop) ∧ validState sf := by
  unfold modelScanFn at hcall
  obtain ⟨words, hdecode, htail⟩ := bind_success (decodeBlock block) _ _ hcall
  obtain ⟨sf', pending, hloop, hpair⟩ := pair_bind_success
    (scanListLoop words.val s)
    (fun sf pending => .ok (optionStop pending, sf))
    (stop, sf) htail
  have hvals : optionStop pending = stop ∧ sf' = sf := by
    injection (Result.ok.inj hpair) with hstop hsf
    exact ⟨hstop, hsf⟩
  obtain ⟨sf0, pending0, hmodel, hscan, hvalid⟩ := scanListLoop_q22_valid words.val s hs
  have hsame : (sf0, pending0) = (sf', pending) :=
    Result.ok.inj (hmodel.symm.trans hloop)
  rcases hsame with ⟨rfl, rfl⟩
  have hpair' : (optionStop pending, sf') = (stop, sf) := Result.ok.inj hpair
  have hstop : optionStop pending = stop := congrArg Prod.fst hpair'
  have hsf : sf' = sf := congrArg Prod.snd hpair'
  refine ⟨words, hdecode, ?_, ?_⟩
  · cases hsf
    cases hstop
    exact hscan
  · cases hsf
    exact hvalid

#print axioms modelScanFn_success
end Query31ModelScanCall
