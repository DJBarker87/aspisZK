import S2SdkSourceScanV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS2SdkScanFission
open AspisS2OwnedStage1 AspisS2OwnedStage1.SdkReference
open AspisS2StdAnySource AspisS2SdkIterator

/-- Actual extracted scanner/iterator instance, with the one overwritten
scan-result ghost. The original full SDK remains immutable; this is a ghost
extension, never a replacement SDK/account/guard carrier. The actual native
enter/leave footprints and probe safety are checked separately in Kani. -/
def recordedScan (sdk : OwnedSdk) (slot : Usize) (_old : Option Bool) :
    Result (Bool × Option Bool) := do
  let iter ← source_begin sdk slot
  let (hit,_) ← sourceAny (next sdk) nonzeroPredicate (wrap iter) ()
  ok (hit,some hit)

/-- Erasing the recorded value preserves the COMPLETE emitted computation,
including invalid-slot errors and divergence. Exactly one begin/any is used;
there is no additional traversal, reordering or ghost-dependent branch. -/
theorem erase_recorded (sdk : OwnedSdk) (slot : Usize) (old : Option Bool) :
    (do let (hit,_) ← recordedScan sdk slot old; ok hit)=sourceScan sdk slot := by
  unfold recordedScan sourceScan
  cases begin : source_begin sdk slot with
  | fail error => simp only [begin,bind_tc_fail]
  | div => simp only [begin,bind_tc_div]
  | ok iter =>
    simp only [begin,bind_tc_ok]
    cases step : sourceAny (next sdk) nonzeroPredicate (wrap iter) () with
    | fail error => simp only [step,bind_tc_fail]
    | div => simp only [step,bind_tc_div]
    | ok pair => rcases pair with ⟨hit,out⟩;rfl

/-- The overwrite is the same hit returned by the same scan, for every old
value. No separately chosen ghost observation is accepted as a scan result. -/
theorem reported_value (sdk : OwnedSdk) (slot : Usize) (old reported : Option Bool) (hit : Bool)
    (run : recordedScan sdk slot old=ok (hit,reported)) : reported=some hit := by
  unfold recordedScan at run
  cases begin : source_begin sdk slot with
  | fail error => simp only [begin,bind_tc_fail] at run; cases run
  | div => simp only [begin,bind_tc_div] at run; cases run
  | ok iter =>
    simp only [begin,bind_tc_ok] at run
    cases step : sourceAny (next sdk) nonzeroPredicate (wrap iter) () with
    | fail error => simp only [step,bind_tc_fail] at run; cases run
    | div => simp only [step,bind_tc_div] at run; cases run
    | ok pair =>
      rcases pair with ⟨actual,out⟩
      simp only [step,bind_tc_ok,Aeneas.Std.uncurry] at run
      cases run
      rfl

/-- A native-style Some(false) report identifies the actual scanner outcome;
the output hit cannot be supplied independently. -/
theorem reported_false (sdk : OwnedSdk) (slot : Usize) (old : Option Bool) (hit : Bool)
    (run : recordedScan sdk slot old=ok (hit,some false)) : sourceScan sdk slot=ok false := by
  have report := reported_value sdk slot old (some false) hit run
  have same : hit=false := (Option.some.inj report).symm
  subst hit
  rw [←erase_recorded sdk slot old,run]
  rfl

/-- Consume the existing TOTAL scanner/iterator/clone laws to obtain zero
original bytes from that SAME recorded scan. No traversal success, byte-zero
premise, new parser proof or source-iterator contract is introduced. -/
theorem reported_false_zero (sdk : OwnedSdk) (slot : Usize) (old : Option Bool) (hit : Bool)
    (cell : OwnedDataCell)
    (read : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedDataCell)
      sdk.data_cells slot=ok cell)
    (run : recordedScan sdk slot old=ok (hit,some false)) :
    ∀ byte ∈ cell.bytes.val,byte=0#u8 := by
  have scan := reported_false sdk slot old hit run
  have snapshot : snapshotScan sdk slot=ok false :=
    (snapshotScan_eq_sourceScan sdk slot).trans scan
  simp only [snapshotScan,read,bind_tc_ok,PrimitivesTotal.bytes_clone_total] at snapshot
  rw [ScanTotal.scan_eq,CheckpointGuardTransport.owned_eq_std] at snapshot
  exact (CheckpointGuardTransport.stdAny_false cell.bytes.val).mp (Result.ok.inj snapshot)

#print axioms erase_recorded
#print axioms reported_value
#print axioms reported_false
#print axioms reported_false_zero
end AspisS2SdkScanFission
