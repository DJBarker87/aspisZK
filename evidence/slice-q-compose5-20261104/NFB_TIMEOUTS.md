NFB_K012: actual-root invalid-range shape timed out at Kani's unchanged 90s
harness limit (93.608s scope, 1,670,220KiB, swap0). The solver did not establish
unreachability of the body cheaply. No semantic pass or field-product proof
is claimed. This shape will never be repeated. Replacement: the exact scalar
guard fission NFB_guard, checked against the frozen source; body/root association
still requires the full extracted Result and native phase packet.

NFB_K069: Kani compiler ICE on the raw row-pointer observation shape, before
verification (1.578s, 241504KiB, swap0). No control or semantic credit.
Replacement keeps the exact std store helper and original harness names;
observations/controls use scalar element reads/writes at 5*row+lane, with an
explicit row-size equality. No tool or launcher patch and no cap increase.

NFB_K070: same compiler assertion `length >= min_length`, still before
verification (1.780s, 242264KiB, swap0). Source inspection identifies a smaller
input issue: fixed guarded setup uses `old[10]`/`old[11]` in the N=10
monomorph. Built MIR retains those unreachable constant-index projections,
which Kani rejects before guard reasoning. Replace ONLY guarded setup reads
with raw-pointer reads under the same bounds, as in NEW's reserve setup.
This corrects the earlier tentative raw-row-observation diagnosis. Harness
names and the exact store/finalization bodies remain unchanged; both ICE
receipts are excluded. No tool patch or cap change.

NFB_K071 reached verification but failed an unwinding assertion at unwind2
(4.989s,408896KiB,swap0); it was not a timeout and has no credit. Replacement
removes artificial bulk setup copies: use the actual Vec::with_capacity
constructor, and flat60 scalar havoc rather than nested-array havoc and an
uninitialized Box array. Guarded scalar writes initialize ONLY the live
prefix. The frozen one-store body is unchanged. Unwind7 covers only fixed
five-cell row moves / tiny guard primitives; the source loop still has ONE
arbitrary iteration, never a whole collection. No time or memory cap changes.

L065: kernel excessive memory at -M7000, RSS7168772KiB, exit1, swap0.
The concrete dictionary rewrite followed by rfl expanded irrelevant operations
while checking a backward body that mathematically depends ONLY on op9.
Excluded. Replacement: prove generic body/loop congruence for an abstract Ops
pair and one multiplication-field equality, then specialize by theorem
application; no concrete dictionary reduction, no cap increase or unchanged rerun.
