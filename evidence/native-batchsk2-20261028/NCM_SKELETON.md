# NCM skeleton assembly

Stage 1 COMPLETE: AspisR1.NCM_U09.bridge and AspisR1.NCM_Batch.bridge
compile and are audited in NCM_L072. These are CONDITIONAL compositions.
All 18 native fragments remain OPEN; no deployed/native closure is claimed.

Target: AspisR1.RPx_Deployed.deployed, frozen3; L154 is a statement parameter,
D188 is narrowed; RuntimePersistence remains the approved trust item.
The 18 exact NCE native fragment statements are imported read-only from the
NCE_ROOT_INVENTORY.json union. The pinned elaborated statements are retained
verbatim in NCM_NATIVE_STATEMENTS.txt (copied, not re-proved).

The existing batch cache is reused in place, never deleted. Sources/launchers
are private under codex-cx-native-batchsk2-20261028. NCM_INITIAL_HOST_PINS.json
records imported object hashes; NCM_RESOLVED_AENEAS_PINS.json pins Aeneas at
the actual LEAN_PATH resolution. Each compile pins its direct object hashes.
Own scripts derive from NCE scripts; only prefix, private workspace and budget
limits (80 Lean / 50 Kani) changed. Admission still requires allowed:true AND
exit 0, before upload and launch. One scope at a time; fixed caps and -M7000.

## Composition order

1. Native row progress on the SAME carrier from the existing row cut.
2. Rows, exhausted-row control and levels, preserving exact rejected prefix.
3. Verifier admission/final guard; leaf/key/opening/count/padding join.
4. Three trees and the two requested bridge statements, with U00/provenance
   lower boundaries explicitly named rather than whole-item conclusions.

No shipped source, cfg(kani) module or release artifact has changed.

## Exact imported native hypothesis statements

These are the 18 immutable elaborated NCE statements. None has yet been
discharged natively by NCM. Local interpreter parameters remain explicit.

```text
def AspisR1.NCE_AdmissionCuts.NCE_Native_Admission : AspisR1.NCE_AdmissionCuts.Predicate →
  AspisR1.NCE_AdmissionCuts.Predicate → Prop :=
fun pair range =>
  (∀ (s : AspisR1.NCE_OpeningCuts.Carrier) (i : ℕ),
      ↑s.scratch.n ≤ 16 →
        i + 1 < ↑s.scratch.n →
          pair s i = (decide (AspisR1.NCE_AdmissionCuts.index s i < AspisR1.NCE_AdmissionCuts.index s (i + 1)), s)) ∧
    ∀ (s : AspisR1.NCE_OpeningCuts.Carrier) (i : ℕ),
      ↑s.scratch.n ≤ 16 → i < ↑s.scratch.n → range s i = (decide (AspisR1.NCE_AdmissionCuts.index s i < 262144), s)
def AspisR1.NCE_CarrierEffects.NCE_Native_Row : (AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State) →
  AspisR1.NCE_CarrierEffects.Node → Prop :=
fun H native =>
  ∀ (caller : AspisR1.NCE_OpeningCuts.Carrier) (physical : Aeneas.Std.Slice Aeneas.Std.U8) (i w : Aeneas.Std.Usize),
    (↑physical).length ≤ 5504 →
      AspisR1.MultiproofConeNodeDomain.RowDomain physical caller.scratch i w →
        ↑i < ↑caller.scratch.n →
          AspisV8R19.MemoizedProgramLaw.eval H (native caller physical i w) =
            AspisV8R19.MemoizedProgramLaw.eval H
              (AspisR1.NCE_CarrierEffects.annotate AspisR1.NCE_CarrierEffects.rowScratch caller
                (AspisR1.MultiproofConePhysicalTransport.transport
                  (AspisR1.MultiproofConePhysicalProgram.node caller.scratch physical i w)))
def AspisR1.NCE_CountCuts.NCE_Native_CountScan : {Frame : Type} →
  (AspisR1.NCE_CountCuts.ScanState Frame → Bool × AspisR1.NCE_CountCuts.ScanState Frame) → Prop :=
fun {Frame} native =>
  ∀ (s : AspisR1.NCE_CountCuts.ScanState Frame),
    AspisR1.NCE_CountCuts.ScanDomain s →
      (native s).1 = decide (s.cursor < s.n ∧ s.key s.cursor / 2 = s.parent) ∧
        ((native s).2.cursor = if s.cursor < s.n ∧ s.key s.cursor / 2 = s.parent then s.cursor + 1 else s.cursor) ∧
          (∀ (k : ℕ), (native s).2.key k = s.key k) ∧
            (native s).2.n = s.n ∧ (native s).2.parent = s.parent ∧ (native s).2.frame = s.frame
def AspisR1.NCE_CountInitCuts.NCE_Native_CountZero : {Frame : Type} →
  ((ℕ → ℕ) → ℕ → Frame → AspisR1.NCE_CountInitCuts.InitState Frame) → Prop :=
fun {Frame} create =>
  ∀ (source : ℕ → ℕ) (n : ℕ) (frame : Frame),
    n ≤ 16 →
      (∀ (k : ℕ), (create source n frame).memory k = 0) ∧
        (∀ (k : ℕ), (create source n frame).source k = source k) ∧
          (create source n frame).cursor = 0 ∧ (create source n frame).n = n ∧ (create source n frame).frame = frame
def AspisR1.NCE_CountInitCuts.NCE_Native_CountCopy : {Frame : Type} →
  (AspisR1.NCE_CountInitCuts.InitState Frame → AspisR1.NCE_CountInitCuts.InitState Frame) → Prop :=
fun {Frame} copy =>
  ∀ (s : AspisR1.NCE_CountInitCuts.InitState Frame),
    s.cursor < s.n →
      s.n ≤ 16 →
        (∀ k < s.n, s.source k < 262144) →
          (∀ (k : ℕ), (copy s).memory k = if k = s.cursor then s.source s.cursor else s.memory k) ∧
            (∀ (k : ℕ), (copy s).source k = s.source k) ∧
              (copy s).cursor = s.cursor + 1 ∧ (copy s).n = s.n ∧ (copy s).frame = s.frame
def AspisR1.NCE_CountLevelCuts.NCE_Native_CountHeight : {Frame : Type} →
  (AspisR1.NCE_CountRowCuts.RowState (ℕ × Frame) → AspisR1.NCE_CountLevelCuts.LevelState Frame) → Prop :=
fun {Frame} native =>
  ∀ (s : AspisR1.NCE_CountRowCuts.RowState (ℕ × Frame)),
    s.w ≤ 16 →
      s.frame.1 < 18 →
        (∀ (k : ℕ), (native s).key k = s.key k) ∧
          (native s).n = s.w ∧
            (native s).count = s.count ∧ (native s).depth = s.frame.1 + 1 ∧ (native s).frame = s.frame.2
def AspisR1.NCE_CountRowCuts.NCE_Native_CountCommit : {Frame : Type} →
  (AspisR1.NCE_CountRowCuts.RowState Frame → ℕ → AspisR1.NCE_CountRowCuts.RowState Frame) → Prop :=
fun {Frame} native =>
  ∀ (s : AspisR1.NCE_CountRowCuts.RowState Frame) (j : ℕ),
    AspisR1.NCE_CountRowCuts.CommitDomain s j →
      (∀ (k : ℕ), (native s j).key k = if k = s.w then s.key s.i / 2 else s.key k) ∧
        (native s j).n = s.n ∧
          (native s j).i = j ∧
            (native s j).w = s.w + 1 ∧ (native s j).count = s.count + (2 - (j - s.i)) ∧ (native s j).frame = s.frame
def AspisR1.NCE_KeyCuts.NCE_Native_KeysWrite : (AspisR1.NCE_KeyCuts.KeyState → AspisR1.NCE_KeyCuts.KeyState) → Prop :=
fun native =>
  ∀ (s : AspisR1.NCE_KeyCuts.KeyState),
    s.batch < 2 →
      s.kind < 3 →
        s.cursor < AspisR1.NCE_KeyCuts.count s →
          AspisR1.NCE_KeyCuts.canonical s →
            (native s).caller = s.caller ∧
              (native s).batch = s.batch ∧
                (native s).kind = s.kind ∧
                  (native s).cursor = s.cursor + 1 ∧
                    ↑((native s).keys s.cursor) =
                        (256 *
                            if s.kind = 2 then ↑(↑s.caller.prepared.queries)[AspisR1.NCE_KeyCuts.lo s + s.cursor]! / 4
                            else ↑(↑s.caller.prepared.queries)[AspisR1.NCE_KeyCuts.lo s + s.cursor]!) +
                          s.cursor ∧
                      ∀ (k : ℕ), k ≠ s.cursor → (native s).keys k = s.keys k
def AspisR1.NCE_KeyProducerCuts.NCE_Native_KeysZero : (AspisR1.NCE_OpeningCuts.Carrier →
    ℕ → ℕ → AspisR1.NCE_KeyCuts.KeyState) →
  Prop :=
fun create =>
  ∀ (caller : AspisR1.NCE_OpeningCuts.Carrier) (batch kind : ℕ),
    batch < 2 →
      kind < 3 →
        (∀ (k : ℕ), (create caller batch kind).keys k = 0#u64) ∧
          (create caller batch kind).caller = caller ∧
            (create caller batch kind).cursor = 0 ∧
              (create caller batch kind).batch = batch ∧ (create caller batch kind).kind = kind
def AspisR1.NCE_KeyReadCuts.NCE_Native_KeysRead : AspisR1.NCE_KeyReadCuts.Read → Prop :=
fun native =>
  ∀ (caller : AspisR1.NCE_OpeningCuts.Carrier) (keys : Aeneas.Std.Array Aeneas.Std.U64 16#usize)
    (cursor : Aeneas.Std.Usize),
    ↑cursor < 16 →
      native caller keys cursor = Aeneas.Std.Result.ok ((↑keys)[↑cursor]!, cursor.wrapping_add 1#usize, keys, caller)
def AspisR1.NCE_LeafCuts.NCE_Native_Leaf : AspisR1.NCE_LeafCuts.Request → AspisR1.NCE_LeafCuts.Post → Prop :=
fun request post =>
  (∀ {X : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 X) (hash : X) (kind : Aeneas.Std.Usize)
      (view : Aeneas.Std.Slice Aeneas.Std.U8) (before : AspisR1.CheckpointBytes5Effect.Log),
      ↑kind < 3 →
        (↑view).length = 832 →
          AspisR1.CheckpointBytes5Effect.run D hash (request kind view) before =
            AspisR1.CheckpointBytes5Effect.run D hash (AspisR1.Port4B_LeafCode.code kind view) before) ∧
    ∀ (s : AspisR1.NCE_OpeningCuts.Carrier) (index : Aeneas.Std.U32) (reply : AspisR1.CheckpointBytes5Effect.Digest)
      (pos : Aeneas.Std.Usize),
      ↑s.scratch.n < 16 →
        post s index reply pos = do
          let out ← AspisR1.Port4B_LeafStep.post s.scratch.idx s.scratch.val s.scratch.n index reply pos
          Aeneas.Std.Result.ok (out, AspisR1.NCE_LeafCuts.returnedCarrier s out)
def AspisR1.NCE_OpeningCuts.NCE_Native_Opening : AspisR1.NCE_OpeningCuts.Reader → Prop :=
fun reader =>
  ∀ (s : AspisR1.NCE_OpeningCuts.Carrier) (i w c : ℕ),
    (↑s.proof).length = 57607 →
      i < 22 →
        w < 26 →
          c < 32 →
            reader s (10055 + 832 * i + 32 * w + c) =
              Aeneas.Std.Result.ok ((↑s.proof)[10055 + 832 * i + 32 * w + c]!, s)
def AspisR1.NCE_OuterCuts.NCE_Native_ThreeTrees : AspisR1.NCE_OuterCuts.Start →
  AspisR1.NCE_OuterCuts.Continue → AspisR1.NCE_OuterCuts.Continue → AspisR1.NCE_OuterCuts.Finish → Prop :=
fun start after0 after1 finish =>
  (∀ (s : AspisR1.NCE_OpeningCuts.Carrier), start s = (0, s)) ∧
    (∀ (accepted : Bool) (s : AspisR1.NCE_OpeningCuts.Carrier),
        after0 (accepted, s) =
          if accepted = true then AspisR1.NCE_OuterCuts.Next.call 1 s else AspisR1.NCE_OuterCuts.Next.stop s) ∧
      (∀ (accepted : Bool) (s : AspisR1.NCE_OpeningCuts.Carrier),
          after1 (accepted, s) =
            if accepted = true then AspisR1.NCE_OuterCuts.Next.call 2 s else AspisR1.NCE_OuterCuts.Next.stop s) ∧
        ∀ (accepted : Bool) (s : AspisR1.NCE_OpeningCuts.Carrier),
          finish (accepted, s) = (if accepted = true then none else some 2, s)
def AspisR1.NCE_PaddingCuts.NCE_Native_Padding : {Frame : Type} →
  Aeneas.Std.core.ops.function.FnMut Unit (Aeneas.Std.Slice Aeneas.Std.U8) Bool →
    AspisR1.NCE_PaddingCuts.Body Frame → Prop :=
fun {Frame} predicate native =>
  ∀ (it : AspisR1.NCE_PaddingCuts.Iter) (frame : Frame),
    (∀ c ∈ it.chunks, (↑c).length = 8) → native (it, frame) = AspisR1.NCE_PaddingCuts.body predicate (it, frame)
def AspisR1.NCE_RowStoreCuts.NCE_Native_RowStore : AspisR1.NCE_RowStoreCuts.Store → Prop :=
fun native =>
  ∀ (s : AspisR1.NCE_OpeningCuts.Carrier) (w : Aeneas.Std.Usize) (parent : Aeneas.Std.U32)
    (digest : AspisR1.NCE_RowStoreCuts.Digest) (cursor : Aeneas.Std.Usize),
    ↑w < 16 →
      (native s w parent digest cursor).prepared = s.prepared ∧
        (native s w parent digest cursor).proof = s.proof ∧
          (native s w parent digest cursor).log = s.log ∧
            (native s w parent digest cursor).scratch.n = s.scratch.n ∧
              (native s w parent digest cursor).scratch.at = cursor ∧
                (∀ j < 16,
                    (↑(native s w parent digest cursor).scratch.idx)[j]! =
                      if j = ↑w then parent else (↑s.scratch.idx)[j]!) ∧
                  ∀ (j c : ℕ),
                    j < 16 →
                      c < 32 →
                        (↑(↑(native s w parent digest cursor).scratch.val)[j]!)[c]! =
                          if j = ↑w then (↑digest)[c]! else (↑(↑s.scratch.val)[j]!)[c]!
def AspisR1.NCE_SortCarrierCuts.NCE_Native_KeysSortCarrier : AspisR1.NCE_SortCarrierCuts.Step → Prop :=
fun native =>
  ∀ (caller : AspisR1.NCE_OpeningCuts.Carrier) (keys : Aeneas.Std.Array Aeneas.Std.U64 16#usize)
    (cursor : Aeneas.Std.Usize),
    ↑cursor < 16 →
      ∃ out,
        native caller keys cursor = Aeneas.Std.Result.ok (out, caller) ∧ AspisR1.NBI_Sort.NativeStep keys cursor out
def AspisR1.NCE_SortCuts.NCE_Native_KeysSort : AspisR1.NCE_SortCuts.Step → Prop :=
fun native =>
  ∀ (keys : Aeneas.Std.Array Aeneas.Std.U64 16#usize) (cursor : Aeneas.Std.Usize),
    ↑cursor < 16 → ∃ out, native keys cursor = Aeneas.Std.Result.ok out ∧ AspisR1.NBI_Sort.NativeStep keys cursor out
def AspisR1.NCE_VerifierCuts.NCE_Native_Verifier : AspisR1.NCE_VerifierCuts.Entry →
  AspisR1.NCE_VerifierCuts.Exit → AspisR1.NCE_VerifierCuts.Finish → Prop :=
fun entry exit finish =>
  (∀ (s : AspisR1.NCE_OpeningCuts.Carrier) (bytes : ℕ) (valid : Bool),
      bytes ≤ 5504 →
        entry s bytes valid = (decide (0 < ↑s.scratch.n ∧ ↑s.scratch.n ≤ 16 ∧ bytes % 32 = 0) && valid, s)) ∧
    (∀ (s : AspisR1.NCE_OpeningCuts.Carrier) (w : Aeneas.Std.Usize),
        ↑w ≤ 16 →
          exit s w =
            { prepared := s.prepared, proof := s.proof,
              scratch :=
                have __src := s.scratch;
                { idx := __src.idx, val := __src.val, n := w, «at» := __src.at },
              log := s.log }) ∧
      ∀ (s : AspisR1.NCE_OpeningCuts.Carrier) (root : AspisR1.NCE_VerifierCuts.Digest)
        (physical : Aeneas.Std.Slice Aeneas.Std.U8),
        ↑s.scratch.n ≤ 16 →
          ↑s.scratch.at ≤ (↑physical).length →
            (↑physical).length ≤ 5504 →
              finish s root physical =
                (decide
                    (↑s.scratch.n = 1 ∧
                      ↑(↑s.scratch.idx)[0]! = 0 ∧ (↑s.scratch.val)[0]! = root ∧ ↑s.scratch.at = (↑physical).length),
                  s)
```

## Assembly audit

The complete top statements are generated with 18 **separate** native Prop
parameters by NCM_params.py/NCM_assembly.py; Ops contains function data only.
NCM_BatchTypes.Inputs contains only original proof length/wire identity,
canonical actual Prepared queries, its two root projections and the actual
folded-root argument. The enclosing U00/prepare/resume provenance must establish
those exact input facts; this packet does not claim those lower native bridges
closed. Inputs contains no result, successful child, count, padding scan or log.

The old value-only KeysSort family is superseded by KeysSortCarrier; RowStore
is already included in the complete single-row observation. Both requested
weak families remain explicit and undischarged in the 18-parameter audit.
Their redundancy is not counted as premise removal or native discharge.

The direct child observer reads newly issued events from the actual carried
log by removing only its already-issued initial prefix. It never turns a log
into Program asks, reruns a digest, erases a rejecting suffix, or substitutes
an independently selected result. On the proved domain every raw request and
native leaf continuation returns a checked value, including duplicate error.

Rejected physical scratch is preserved in the native observer. The cohort
slot discards it on leaf error; equality is therefore asserted for result and
chronological reads on every outcome, and for scratch on acceptance. Later
trees are never called after rejection. This is the adopted L166 observation,
not exact Rust error-enum identity or an unsupported rejected-scratch equality.

## Exact final observation and validation

NCM_Assembly.Claim compares the SAME carrier/proof/Prepared/folded argument
against the existing cohort three-tree observation. It asserts chronological
trace equality, equal first failing tree (or acceptance), unchanged Prepared
and proof, log=old log++issued trace, and scratch equality on acceptance.
Batch.bridge fixes batch=0; U09.bridge fixes batch=1. No native hypothesis
asserts a complete tree/batch result. D.digest realization is the named oracle
law; Inputs is exactly the provenance record printed in NCM_BatchTypes.lean.

Focused tops: L070 Batch exit0, 2.198934s, peak4435136KiB, swaps0;
L071 U09 exit0, 1.984242s, peak4435256KiB, swaps0. Final audit L072 exit0,
1.714032s, peak4417024KiB, swaps0. All 61 new theorem roots print subsets
of propext/Classical.choice/Quot.sound. Source revision at these attempts:
8270797d0c11f0831e9a97889f08dfe869b23b9e, dirty NCM sources pinned by sha256
in each receipt. Exact commands/objects/limits are in those receipts.
This is a focused cached closure audit, not a frozen release manifest replay.
