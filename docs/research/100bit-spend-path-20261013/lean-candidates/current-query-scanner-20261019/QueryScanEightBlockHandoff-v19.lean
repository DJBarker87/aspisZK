import QueryScanFiniteCorrespondence
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
namespace AspisR1QueryScanUnrolled.r0_transcript
open AspisV8R19.Q22WordScan

def queryWordsOfList (xs : List Std.U32) : List Nat := xs.map (fun x => x.val)
def queryBlocksWords (blocks : List (List Std.U32)) : List Nat :=
  blocks.flatMap queryWordsOfList
inductive EightBlockRun {A : Type} (advance : Nat → A) (fallback : A) :
    Nat → List (List Std.U32) → QueryScan → QueryScan → A → Bool → Prop where
  | nil (k : Nat) (s : QueryScan)
      (hlen : s.accepted_len.val ≤ 22) (hdraw : s.draws.val ≤ 64) :
      EightBlockRun advance fallback k [] s s fallback false
  | stopped (k : Nat) (block : List Std.U32) (blocks : List (List Std.U32))
      (s sf : QueryScan)
      (hlen : s.accepted_len.val ≤ 22) (hdraw : s.draws.val ≤ 64)
      (hscan : QueryScan.scan_loop block s = .ok (sf, q22Option true)) :
      EightBlockRun advance fallback k (block :: blocks) s sf (advance k) true
  | more (k : Nat) (block : List Std.U32) (blocks : List (List Std.U32))
      (s sf sf' : QueryScan) (selected : A) (stopped : Bool)
      (hlen : s.accepted_len.val ≤ 22) (hdraw : s.draws.val ≤ 64)
      (hscan : QueryScan.scan_loop block s = .ok (sf, q22Option false))
      (tail : EightBlockRun advance fallback (k+1) blocks sf sf' selected stopped) :
      EightBlockRun advance fallback k (block :: blocks) s sf' selected stopped

private theorem queryscan_q22_finite_correspondence_bounded (s : QueryScan)
    (xs : List Std.U32)
    (hlen : s.accepted_len.val ≤ 22) (hdraw : s.draws.val ≤ 64) :
    ∃ sf stopped,
      QueryScan.scan_loop xs s = .ok (sf, q22Option stopped) ∧
      scan (q22StateOfFresh s) (xs.map (fun x => x.val)) =
        (q22StateOfFresh sf, stopped) ∧
      sf.accepted_len.val ≤ 22 ∧ sf.draws.val ≤ 64 := by
  induction xs generalizing s with
  | nil =>
      refine ⟨s, false, scan_loop_empty s, ?_, hlen, hdraw⟩
      simp [q22Option, scan]
  | cons x xs ih =>
      by_cases hstop : s.accepted_len = QUERY_COUNT ∨ s.draws = QUERY_MAX_DRAWS
      · obtain ⟨hsource, hmodel⟩ :=
          scan_loop_stopped_q22 s x xs (q22StateOfFresh s) rfl hstop
        exact ⟨s, true, by simpa [q22Option] using hsource,
          by simpa using hmodel, hlen, hdraw⟩
      · have hlenLt : s.accepted_len.val < 22 := by
          by_contra hnot
          have hv : s.accepted_len.val = QUERY_COUNT.val := by
            simp [QUERY_COUNT]
            omega
          exact hstop (Or.inl (UScalar.eq_of_val_eq hv))
        have hdrawLt : s.draws.val < 64 := by
          by_contra hnot
          have hv : s.draws.val = QUERY_MAX_DRAWS.val := by
            simp [QUERY_MAX_DRAWS]
            omega
          exact hstop (Or.inr (UScalar.eq_of_val_eq hv))
        have hactive := active_q22_of_bounded_source s hlenLt hdrawLt
        have hnext :
            @core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next U32 (8#usize) (x :: xs) =
              ok (some x, xs) := by rfl
        by_cases hfresh : x.val ∉ acceptedPrefix s
        · obtain ⟨drawNext, lenNext, a, hdrawOp, hdrawVal, hlenOp, hlenVal,
              hupdate, hbody, hstate⟩ :=
            scan_body_fresh_from_bounds (x :: xs) s x xs hnext hlenLt hdrawLt hfresh
          let s' : QueryScan := { s with accepted := a, accepted_len := lenNext, draws := drawNext }
          have hlen' : s'.accepted_len.val ≤ 22 := by simp [s', hlenVal]; omega
          have hdraw' : s'.draws.val ≤ 64 := by simp [s', hdrawVal]; omega
          obtain ⟨sf, stopped, hsourceTail, hmodelTail, hlenSf, hdrawSf⟩ := ih s' hlen' hdraw'
          have hunroll := scan_loop_cons_unroll x xs s s' hbody
          have hmodelStep := q22_scan_cons_fresh_unroll (q22StateOfFresh s) x.val
            (xs.map (fun y => y.val)) hactive hfresh
          have hmodelStep' : scan (q22StateOfFresh s) (x.val :: xs.map (fun y => y.val)) =
              scan (⟨acceptedPrefix s ++ [x.val], s.draws.val + 1⟩ : ScanState)
                (xs.map (fun y => y.val)) := by simpa [q22StateOfFresh] using hmodelStep
          refine ⟨sf, stopped, ?_, ?_, hlenSf, hdrawSf⟩
          · rw [hunroll, hsourceTail]
          · rw [List.map_cons]
            rw [hmodelStep', ← hstate, hmodelTail]
        · have hmember : x.val ∈ acceptedPrefix s := by
            by_contra hmem
            exact hfresh hmem
          obtain ⟨drawNext, hdrawOp, hdrawVal, hbody, hstate⟩ :=
            scan_body_duplicate_from_bounds (x :: xs) s x xs hnext hlenLt hdrawLt hmember
          let s' : QueryScan := { s with draws := drawNext }
          have hlen' : s'.accepted_len.val ≤ 22 := by simpa [s'] using hlen
          have hdraw' : s'.draws.val ≤ 64 := by simp [s', hdrawVal]; omega
          obtain ⟨sf, stopped, hsourceTail, hmodelTail, hlenSf, hdrawSf⟩ := ih s' hlen' hdraw'
          have hunroll := scan_loop_cons_unroll x xs s s' hbody
          have hmodelStep := q22_scan_cons_duplicate_unroll (q22StateOfFresh s) x.val
            (xs.map (fun y => y.val)) hactive hmember
          have hmodelStep' : scan (q22StateOfFresh s) (x.val :: xs.map (fun y => y.val)) =
              scan (⟨acceptedPrefix s, s.draws.val + 1⟩ : ScanState)
                (xs.map (fun y => y.val)) := by simpa [q22StateOfFresh] using hmodelStep
          refine ⟨sf, stopped, ?_, ?_, hlenSf, hdrawSf⟩
          · rw [hunroll, hsourceTail]
          · rw [List.map_cons]
            rw [hmodelStep', ← hstate, hmodelTail]

private theorem acceptedPrefix_length_eq (s : QueryScan)
    (hlen : s.accepted_len.val ≤ 22) :
    (acceptedPrefix s).length = s.accepted_len.val := by
  simp [acceptedPrefix, List.length_take, s.accepted.property, Nat.min_eq_left hlen]

private theorem scan_loop_bounds_after
    (s sf : QueryScan) (xs : List Std.U32)
    (hlen : s.accepted_len.val ≤ 22) (hdraw : s.draws.val ≤ 64)
    (hscan : QueryScan.scan_loop xs s = .ok (sf, q22Option false)) :
    sf.accepted_len.val ≤ 22 ∧ sf.draws.val ≤ 64 := by
  obtain ⟨sf0, stop, hrun, hmodel, hlenSf, hdrawSf⟩ :=
    queryscan_q22_finite_correspondence_bounded s xs hlen hdraw
  have hi : (sf0, q22Option stop) = (sf, q22Option false) :=
    Result.ok.inj (hrun.symm.trans hscan)
  have hsf : sf0 = sf := congrArg Prod.fst hi
  have hstop : stop = false := by
    cases stop <;> simp [q22Option] at hi ⊢
  subst sf0
  subst stop
  exact ⟨hlenSf, hdrawSf⟩

theorem eightBlockRun_exists {A : Type} (advance : Nat → A) (fallback : A)
    (k : Nat) (blocks : List (List Std.U32)) (s : QueryScan)
    (hlen : s.accepted_len.val ≤ 22) (hdraw : s.draws.val ≤ 64) :
    ∃ sf selected stopped, EightBlockRun advance fallback k blocks s sf selected stopped := by
  induction blocks generalizing k s with
  | nil => exact ⟨s, fallback, false, .nil k s hlen hdraw⟩
  | cons block blocks ih =>
      obtain ⟨sf, stopped, hscan, _hmodel⟩ :=
        queryscan_q22_finite_correspondence s block hlen hdraw
      by_cases hs : stopped
      · exact ⟨sf, advance k, true, .stopped k block blocks s sf hlen hdraw
          (by simpa [q22Option, hs] using hscan)⟩
      · have hscanFalse : QueryScan.scan_loop block s = .ok (sf, q22Option false) := by
          simpa [q22Option, hs] using hscan
        have hb := scan_loop_bounds_after s sf block hlen hdraw hscanFalse
        obtain ⟨sf', selected, stopped', htail⟩ :=
          ih (k+1) sf hb.1 hb.2
        exact ⟨sf', selected, stopped', .more k block blocks s sf sf' selected stopped'
          hlen hdraw hscanFalse htail⟩

theorem eightBlockRun_selected {A : Type} (advance : Nat → A) (fallback : A)
    (k : Nat) (blocks : List (List Std.U32)) (s sf : QueryScan)
    (selected : A) (stopped : Bool)
    (hRun : EightBlockRun advance fallback k blocks s sf selected stopped) :
    (stopped = false → selected = fallback) ∧
      (stopped = true → ∃ i, i < blocks.length ∧ selected = advance (k+i)) := by
  induction hRun with
  | nil k s hlen hdraw =>
      constructor
      · intro _; rfl
      · intro hs; cases hs
  | stopped k block blocks s sf hlen hdraw hscan =>
      constructor
      · intro hs; cases hs
      · intro _
        refine ⟨0, by simp, ?_⟩
        simp
  | more k block blocks s sf sf' selected stopped hlen hdraw hscan tail ih =>
      constructor
      · intro hs
        exact ih.1 hs
      · intro hs
        obtain ⟨i, hi, hselected⟩ := ih.2 hs
        refine ⟨i+1, ?_, ?_⟩
        · simp; omega
        · have hidx : k + 1 + i = k + (i + 1) := by omega
          rw [hidx] at hselected
          exact hselected

private theorem q22_scan_append_false (q q' : ScanState) (xs ys : List Nat)
    (h : scan q xs = (q', false)) :
    scan q (xs ++ ys) = scan q' ys := by
  induction xs generalizing q with
  | nil =>
      simp [scan] at h
      subst q
      rfl
  | cons x xs ih =>
      by_cases hs : q.accepted.length = 22 ∨ q.draws = 64
      · simp [scan, hs] at h
      · have htail : scan ⟨keep q.accepted x, q.draws+1⟩ xs = (q', false) := by
          simpa [scan, hs] using h
        change scan q (x :: (xs ++ ys)) = scan q' ys
        simp only [scan, if_neg hs]
        exact ih ⟨keep q.accepted x, q.draws+1⟩ htail

private theorem q22_scan_append_true (q q' : ScanState) (xs ys : List Nat)
    (h : scan q xs = (q', true)) :
    scan q (xs ++ ys) = (q', true) := by
  induction xs generalizing q with
  | nil =>
      simp [scan] at h
  | cons x xs ih =>
      by_cases hs : q.accepted.length = 22 ∨ q.draws = 64
      · simpa [scan, hs] using h
      · have htail : scan ⟨keep q.accepted x, q.draws+1⟩ xs = (q', true) := by
          simpa [scan, hs] using h
        change scan q (x :: (xs ++ ys)) = (q', true)
        simp only [scan, if_neg hs]
        exact ih ⟨keep q.accepted x, q.draws+1⟩ htail

theorem eightBlockRun_q22 {A : Type} (advance : Nat → A) (fallback : A)
    (k : Nat) (blocks : List (List Std.U32)) (s sf : QueryScan)
    (selected : A) (stopped : Bool)
    (hRun : EightBlockRun advance fallback k blocks s sf selected stopped) :
    scan (q22StateOfFresh s) (queryBlocksWords blocks) =
      (q22StateOfFresh sf, stopped) := by
  induction hRun with
  | nil k s hlen hdraw =>
      simp [queryBlocksWords, queryWordsOfList, scan]
  | stopped k block blocks s sf hlen hdraw hscan =>
      obtain ⟨sf0, b, hrun, hmodel⟩ :=
        queryscan_q22_finite_correspondence s block hlen hdraw
      have hi : (sf0, q22Option b) = (sf, q22Option true) :=
        Result.ok.inj (hrun.symm.trans hscan)
      have hsf : sf0 = sf := congrArg Prod.fst hi
      have hb : b = true := by
        cases b <;> simp [q22Option] at hi ⊢
      subst sf0
      subst b
      have happend := q22_scan_append_true (q22StateOfFresh s) (q22StateOfFresh sf)
        (queryWordsOfList block) (queryBlocksWords blocks) hmodel
      simpa [queryBlocksWords, queryWordsOfList] using happend
  | more k block blocks s sf sf' selected stopped hlen hdraw hscan tail ih =>
      obtain ⟨sf0, b, hrun, hmodel⟩ :=
        queryscan_q22_finite_correspondence s block hlen hdraw
      have hi : (sf0, q22Option b) = (sf, q22Option false) :=
        Result.ok.inj (hrun.symm.trans hscan)
      have hsf : sf0 = sf := congrArg Prod.fst hi
      have hb : b = false := by
        cases b <;> simp [q22Option] at hi ⊢
      subst sf0
      subst b
      have happend := q22_scan_append_false (q22StateOfFresh s) (q22StateOfFresh sf)
        (queryWordsOfList block) (queryBlocksWords blocks) hmodel
      change scan (q22StateOfFresh s)
        (queryWordsOfList block ++ queryBlocksWords blocks) =
          (q22StateOfFresh sf', stopped)
      rw [happend]
      exact ih

theorem eightBlockRun_selected_eight {A : Type} (advance : Nat → A)
    (blocks : List (List Std.U32)) (s sf : QueryScan)
    (selected : A) (stopped : Bool)
    (hblocks : blocks.length = 8)
    (hRun : EightBlockRun advance (advance 7) 0 blocks s sf selected stopped) :
    (stopped = false → selected = advance 7) ∧
      (stopped = true → ∃ i, i < 8 ∧ selected = advance i) := by
  obtain ⟨hfalse, htrue⟩ := eightBlockRun_selected advance (advance 7) 0 blocks s sf selected stopped hRun
  constructor
  · exact hfalse
  · intro hs
    obtain ⟨i, hi, hsel⟩ := htrue hs
    refine ⟨i, ?_, ?_⟩
    · simpa [hblocks] using hi
    · simpa using hsel

theorem queryScanDefault_q22_initial :
    ∃ s : QueryScan,
      QueryScan.Insts.CoreDefaultDefault.default = .ok s ∧
      s.accepted_len.val = 0 ∧ s.draws.val = 0 ∧
      q22StateOfFresh s = ⟨[], 0⟩ := by
  simp [QueryScan.Insts.CoreDefaultDefault.default, core.default.DefaultArray.default,
    core.default.DefaultU32.default, q22StateOfFresh, acceptedPrefix] <;> rfl

theorem queryScan_scan_q22_of_queryWords
    (s : QueryScan) (block : Array Std.U8 32#usize)
    (words : Array Std.U32 8#usize)
    (hlen : s.accepted_len.val ≤ 22) (hdraw : s.draws.val ≤ 64)
    (hwords : query_words block = .ok words) :
    ∃ sf stopped,
      QueryScan.scan s block = .ok (stopped, sf) ∧
      scan (q22StateOfFresh s) (words.val.map (fun x => x.val)) =
        (q22StateOfFresh sf, stopped) ∧
      sf.accepted_len.val ≤ 22 ∧ sf.draws.val ≤ 64 := by
  obtain ⟨sf, stopped, hloop, hmodel, hlenSf, hdrawSf⟩ :=
    queryscan_q22_finite_correspondence_bounded s words.val hlen hdraw
  refine ⟨sf, stopped, ?_, hmodel, hlenSf, hdrawSf⟩
  simp [QueryScan.scan, hwords, hloop,
    TerminalV4ArrayIntoIterListModel.intoIter,
    Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter] <;>
    cases stopped <;> simp [q22Option]

theorem queryScanEightBlockModel {A : Type} (advance : Nat → A)
    (blocks : List (List Std.U32)) (hblocks : blocks.length = 8) :
    ∃ (s sf : QueryScan) (selected : A) (stopped : Bool),
      QueryScan.Insts.CoreDefaultDefault.default = .ok s ∧
      s.accepted_len.val = 0 ∧ s.draws.val = 0 ∧
      EightBlockRun advance (advance 7) 0 blocks s sf selected stopped ∧
      scan (⟨[], 0⟩ : ScanState) (queryBlocksWords blocks) =
        (q22StateOfFresh sf, stopped) ∧
      ((stopped = false → selected = advance 7) ∧
        (stopped = true → ∃ i, i < 8 ∧ selected = advance i)) := by
  obtain ⟨s, hdefault, hlen, hdraw, hinit⟩ := queryScanDefault_q22_initial
  obtain ⟨sf, selected, stopped, hRun⟩ :=
    eightBlockRun_exists advance (advance 7) 0 blocks s (by omega) (by omega)
  have hmodel := eightBlockRun_q22 advance (advance 7) 0 blocks s sf selected stopped hRun
  have hmodel' : scan (⟨[], 0⟩ : ScanState) (queryBlocksWords blocks) =
      (q22StateOfFresh sf, stopped) := by simpa [hinit] using hmodel
  have hselected := eightBlockRun_selected_eight advance blocks s sf selected stopped hblocks hRun
  exact ⟨s, sf, selected, stopped, hdefault, hlen, hdraw, hRun, hmodel', hselected⟩

#print axioms queryscan_q22_finite_correspondence_bounded
#print axioms scan_loop_bounds_after
#print axioms eightBlockRun_exists
#print axioms eightBlockRun_selected
#print axioms eightBlockRun_selected_eight
#print axioms queryScanDefault_q22_initial
#print axioms queryScan_scan_q22_of_queryWords
#print axioms queryScanEightBlockModel
#print axioms q22_scan_append_false
#print axioms q22_scan_append_true
#print axioms eightBlockRun_q22
end AspisR1QueryScanUnrolled.r0_transcript

