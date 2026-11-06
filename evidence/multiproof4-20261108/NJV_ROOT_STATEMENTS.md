# NJV root statements and hypothesis inventory

Target not yet established. These are complete kernel-printed statements from the focused successful compiles; final combined gate pending.

```lean
theorem NJV_TX2.TX2_093 : ∀ (H : Bytes → State) (root : RefDigest) (physical : Slice U8) (idx : Std.Array U32 16#usize)
  (val : Std.Array RefDigest 16#usize) (n : Usize),
  (↑physical).length ≤ 9216 →
    ∀ (events : List (NJP_RowModel.Request × NJP_RowModel.Digest)) (out : Bool × NJP_RowModel.Scratch),
      NJV_NativeEntry.Invocation (NJP_RequestTransport.hash (rawOracle H)) root physical
          (NJV_EntryABI.initial idx val n) events out →
        (have adopted
```

```lean
theorem NJV_TX2.abort : ∀ (H : Bytes → State) (root : RefDigest) (physical : Slice U8) (idx : Std.Array U32 16#usize)
  (val : Std.Array RefDigest 16#usize) (n : Usize),
  (↑physical).length ≤ 9216 →
    ∀ (events : List (NJP_RowModel.Request × NJP_RowModel.Digest)) (q : NJP_RowModel.Request)
      (pending : NJP_RowModel.Scratch),
      NJV_AbortEntry.Invocation (NJP_RequestTransport.hash (rawOracle H)) root physical (NJV_EntryABI.initial idx val n)
          events q pending →
        (have log
```

```lean
theorem NJV_TX1.TX1_127 : ∀ (H : Bytes → State) (root : RefDigest) (physical : Slice U8) (idx : Std.Array U32 16#usize)
  (val : Std.Array RefDigest 16#usize) (n : Usize),
  (↑physical).length ≤ 9216 →
    ∀ (events : List (NJP_RowModel.Request × NJP_RowModel.Digest)) (out : Bool × NJP_RowModel.Scratch),
      NJV_NativeEntry.Invocation (NJP_RequestTransport.hash (rawOracle H)) root physical
          (NJV_EntryABI.initial idx val n) events out →
        (have adopted
```

```lean
theorem NJV_TX1.abort : ∀ (H : Bytes → State) (root : RefDigest) (physical : Slice U8) (idx : Std.Array U32 16#usize)
  (val : Std.Array RefDigest 16#usize) (n : Usize),
  (↑physical).length ≤ 9216 →
    ∀ (events : List (NJP_RowModel.Request × NJP_RowModel.Digest)) (q : NJP_RowModel.Request)
      (pending : NJP_RowModel.Scratch),
      NJV_AbortEntry.Invocation (NJP_RequestTransport.hash (rawOracle H)) root physical (NJV_EntryABI.initial idx val n)
          events q pending →
        (have log
```

## (aq)(2) inventory

Every returning root has precisely:

- H: the headline byte-oracle slot, with fixed NGC/NJE deployed backend. This is not an arbitrary operation dictionary.
- root/physical/idx/val/n: original arguments of that SAME binary verify_in_place entry. No reselected proof, Prepared, root, array or buffer. The ABI constructs the local cursor as zero.
- bytes: physical length <=9216, the native window domain. NJV_CallerBounds.from_count derives this from the SAME well-formed count input. The original unit's <=10 case and TX2's <=12 case both satisfy the bound; no 96-byte or 5504-byte strengthening.
- events/out: universally quantified observations of that invocation.
- native: ONLY the reviewed parent native cuts after CLOSED child replies are substituted at SAME arguments. Expand NJV_NativeEntry.Invocation -> NJV_NativeLevels.Invocation -> NJV_NativeRows.Invocation -> NJP_NativeRowCut.Cut; NJV_CUTS.md gives every field and native assertion source. These contain local pre/post, frames, counters, arguments and chronological append, not a whole model endpoint equality or child-success premise.

Every abort root substitutes q/pending for the returning out. Its native hypothesis expands NJV_AbortEntry.Invocation -> NJV_AbortLevels/Rows.Invocation -> NJV_Pending.Cut, with exact active/available/input/frame clauses and no reply or Rust Err. The same entry and endpoint occur in the conclusions, as do the exact unanswered request and last-cut domain. Existing syscall trust supplies no runtime totality. There is no assumed caller acceptance, global Run, model endpoint law, free reserve Bool, arbitrary Ops, NoBad, persistence equation or exporter. All per-step child/window/write domains are PROVED internally (NJV_Admission, NJV_RowDomains, NJV_LevelDomains, NJV_AbortDomains). Full arrays/Result/cursor and ordered queries survive the comparison.

The root does not claim the caller's original multiproof unit clauses vanished. NJV_BASELINE_ROWS.json preserves every clause verbatim; NJV_CALLER_INVENTORY.md assigns their discharge at the actual batch_tree occurrence. This is an implementation refinement on a larger own ABI domain, not a changed soundness/security contract. P6/D188 native semantic transport remains explicit option-A RECLASSIFICATION; no trust row is removed or added.
