# Remaining native caller-bound stages

K017/K018: the timed-out expansion K006 is split into low-byte and high-byte
regions at arbitrary row0..28 in the actual464-byte input/928-byte destination.
Both TIMEOUT. No unchanged rerun. The source-region tests remain open; the
prefix/suffix frame harnesses LPc_expand2/3 are UNRUN. LPc.Expand.row_low,
row_high and caller_rows prove only the supplied-model row/byte association.
Peak for this native stage is6667509760B cgroup,6495652KiB RSS,swap0.

K019: wide_view uses arbitrary full57607 proof,13831 semantic and928 y1
buffers, with inactive32 fixed to canonical zero to isolate the non-inactive
frame from inherited K015's arbitrary-inactive test. This distinct split
TIMEOUT. No native general frame result. LPc.View.readset is only the exact
five-range supplied-model law. Native capture/borrow/heap association remains.

K020 PASS: actual ValidatedRecord::decode_k::<28>(0), arbitrary901-byte frame,
rows15..24, arbitrary reached output index0..27. Whenever the actual decoder
returns Ok, all four selected M31 limbs are below P. This checks the actual
semantic_round canonical producer at its actual bound; no child or allocator
stub, no fixed zero payload. LPc.Decode.success_canonical and
LPc.Boundary.decoded_canonical separately derive model coefficients and the
full28 fold's canonical result, with its coefficient0 used twice. The SAME
native returned-array/model carrier association and actual boundary-loop join
remain OPEN. A Kani certificate is not introduced as a Lean axiom.

UNRUN additions in the patch: LPc_check464,LPc_validate116,LPc_decode_reached1,
LPc_expand2/3. Their presence is not verification evidence. The20 Kani runs are
exhausted:8PASS,11TIMEOUT,1compile failure (K004). Native source/params/toolchain
pins and exact resources are retained per receipt, with five exact input-patch
variants. All use the original caps and optimized profile; no memory kill or
swap, no raised cap or timeout, no unchanged timed-out rerun.

Actual-top premise removals remain ZERO. Before/after ARX_Root.deployed and
its quantified families are unchanged: removed/added/changed0/0/0,delta
T0/P0/G0/C0,shared once,SAME witness,L185=L159 alias. No full leaf or deployed
security result is credited. Local canonical/error input classes are inhabited;
joint non-vacuity of the top is not supplied.
