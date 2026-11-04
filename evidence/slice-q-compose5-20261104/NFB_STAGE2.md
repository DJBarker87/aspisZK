Stage 2: native guard and final ownership; exact zero traversal

NFB_L004 proves generic same-owner heap frame and payload extensionality.
NFB_L009 proves private-place disjointness and protected-query prefix frame.
NFB_L013 proves the coherent zero loop equals a finite iterator model on
its exact slice/cursor. It requires only the real remaining-length invariant;
zero short-circuit consumes the word and preserves the actual suffix.
All green theorems have standard-only #print axioms in their receipts.
L003 is an intentionally inverted callback control and fails as intended.
L001/L005-L008/L010-L012 are excluded elaboration failures, retained verbatim.

Native revalidation of NEW zero windows: K002 positive; K003-K007 fail for
stop/cursor/input-frame/selected-word/tag corruption. K008/K009 callback pair;
K010/K011 protected-world pair. These were copied into the job namespace to
revalidate the method, never renamed after a verdict. K013/K014 check the
exact KMX implementation in the original K002 source configuration.

K015/K016 check the exact scalar range guard and its inverted control.
K017/K022 check final record assembly for N=10/N=12, with original line/row
allocation identity, contents at arbitrary row/lane, lengths/capacities, start
and protected input frame. K018-K021/K023-K026 fail for value, start, caller
frame and same-contents/different-allocation corruption respectively.
K027/K028 are the exact-source-configuration KMX pair.
K001 compile failure (missing scratch-only allocator_api feature) is excluded;
NFB_ALLOCATOR.patch fixes only that private input. K012 timeout is excluded
and never repeated; NFB_TIMEOUTS.md records its smaller replacement.

Every run validates the frozen dependency graph, deployed feature closure,
required offline environment and unchanged frozen lock before/after Kani.
Every source snapshot is retained compressed with an uncompressed hash.
The unchanged capped S2W launcher and coherent/cache object pins are retained.
All limits remain 6G/8G/swap0/64, Lean -M7000, optimized Kani; all swaps0.
No shipped source, ELF, wallet, key or authority changed.

Neither root is CLOSED: SAME-buffer phase trace/native-to-model/root
association and validator promotion are still being constructed. The current
row/resize source and NFB_MulDischarge/NFB_ResizeTrace are next-stage WIP,
not evidence of completed obligations until their receipts and controls pass.
