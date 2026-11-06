# NJQ rule-3 library models

No new trust row. These are reviewed standard-library interpretations under (au)(3), the existing Std/AeneasExtraction/P6 boundary. Extraction E001 verified opacity but produced no body; model availability does not imply any decoder row is CLOSED.

## Immutable slice Iterator::any

Pinned documented Rust semantics: `NJQ_PINNED_INPUTS.json` retains the complete nightly-2026-09-17 `core/src/iter/traits/iterator.rs` (SHA256 6a6468cade532beaba7c8b3f0db2b3fa768a069c56b636c68fbf1b27bc7d81a0) and `slice/iter/macros.rs` (8db181ab6087b436dcc4c350efc7283ecc4912e34ca20d8bf7460fca5084c26c). The slice specialization repeatedly takes next, returns true immediately on the first true predicate, and otherwise returns false on exhaustion. The generic default's try_fold/check has the identical Continue/Break recurrence.

Semantics proof: induction on the remaining finite slice. Empty remainder executes no callback, returns false and leaves the exhausted iterator. Nonempty remainder advances once before calling the predicate. A true callback returns immediately with that one-element advance; false recurs on the strict tail with the returned callback state. This is exactly NJI_Any.run/any. NJI_Any.pure_run/value/result already prove the returning pure predicate law by this induction; imported, not duplicated. NJQ_Library adds explicit true/fail/div no-suffix equations. Native Rust predicates have no Rust error arm; fail/div represent abort prefixes, not fabricated Err values.

Domain used by these decoders: valid immutable slice iterator, source position at or before its length, finite remaining slice, zero-capture pure byte predicate `byte != 0` (master/checkpoint) or pure u64 capacity comparison. The root must prove its exact callback law; arbitrary mutable captured callbacks are not licensed by this restricted caller model. Native differential includes local call-count state only to verify one-step/exhaustion behavior; no writable static or function-pointer value is used.

ONE native one-step differential and matched failing control: NJQ_K010 PASS / NJQ_K011 intended assertion FAIL, SAME iterator_any_step name/configuration, exact KMX include and copy_nonoverlapping stub. K009 was an owned erasure-selector preflight failure, no native credit. Arbitrary input byte and predicate threshold; empty/nonempty branches, returned Boolean, consumed remainder and callback count. No whole-buffer native loop. Rule-3 library association is reviewed semantic transcription, not a claim that the absent emitted decoder now exists.

## Mutable slice IterMut::next

The same pinned slice iterator source defines exhaustion as None and otherwise borrows/advances exactly the head, with remaining elements still owned by the iterator. NJQ_IterMut.next is the explicit list/lens model. Its returned lens reconstructs head and suffix on writeback; prefix/tail frames are proved symbolically. Induction over entered steps is the existing NJI_CheckpointLoop proof; no duplicated whole-loop native proof.

Native differential NJQ_K012 PASS; matched failing control NJQ_K013 intended assertion FAIL. Arbitrary two-cell pre-state and replacement, one head write, remaining-cell and exhaustion observations, exact source-array frame. SAME iterator_mut_next_step name, exact KMX configuration. Valid mutable slice and exclusive lifetime ownership are the domain. This does not repair the incompatible emitted IterMut ABI in NJI_L003; no pinned library object or extractor has been edited. A decoder needing an emitted ABI wrapper still needs that association, or the permitted (ah) reference route.
