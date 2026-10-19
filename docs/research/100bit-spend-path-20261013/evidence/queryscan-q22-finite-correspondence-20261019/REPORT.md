# QueryScan finite correspondence packet

This packet freezes the checked finite list-input QueryScan.scan_loop ↔ Q22 recurrence theorem plus its successful proof chain. It does not prove the eight-block queries_from_pairs caller yet.

## Proven result and boundary

AspisR1QueryScanUnrolled.r0_transcript.queryscan_q22_finite_correspondence proves that for an arbitrary finite input list, if the initial source scanner has accepted length ≤22 and draws ≤64, the extracted source loop returns a final source state and stop flag whose accepted-prefix/draw state agrees with the Q22 list recurrence. The proof derives actual active fresh/duplicate source operations under the bounds and uses the exact source stop cases. The scanned list is the input to scan_loop; conversion from the actual byte block to its eight query words, the eight block/advance wrapper, and production adoption are outside this theorem.

The scan implementation is extracted from source revision 9abb1c0619c10997f75e461c015a2f6657817edd. The separately retained feed extraction is an isolated source candidate that factors a by-value feed and unrolls eight calls to avoid Aeneas outer nested-join limitations. It preserves state carry, short circuit, stop-selected advance, and shared finish/error path per its pinned source diff, but it is not the unchanged original source and no production edit/adoption is claimed. The original source cut and LLBC are retained separately.

## Verification

Finite-correspondence target: exit 0, wall 1.706s, peak process RSS 2,472,280 KiB, cgroup sampled peak 280,600,576 bytes, swap 0. Its #print axioms output is in evidence/finite-correspondence/lean.log: [propext, Classical.choice, Quot.sound], no sorryAx. Each exact source, object, receipt, preflight, command and log is grouped by module under sources/, objects/, and evidence/. Receipt/preflight hashes are maintained as copied; SHA256SUMS hashes all payload files except itself.

The Lean proof uses the extracted QueryScan state/body and a list-backed IntoIter semantics adapter already present in the pinned import closure. This is a standard library modeling boundary: the theorem is about the extracted finite list loop under that adapter. It does not yet bridge the eight-element array iterator/queries_from_pairs handoff or sampler semantics.

See extraction/feed-candidate/ and extraction/original-source-cut/ for the exact source/LLBC distinction.
