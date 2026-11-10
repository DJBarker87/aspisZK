# PCWK_ handoff (job pc-prov-p5b, phase P5b)

No difference at a matching configuration was found. No shipped source, ledger row, trust row, RSL or contract changed; no trust row added; nothing pushed.
Frozen source 4bb3b3f. Objects: L187 replay closure by reference. One Lean scope of 12, no extraction. Scope PCWK_L001: exit 0, wall 9.9 s, peak RSS 2.55 GiB, swap 0, caps 6G/8G unraised, source revision 09eac3b9008.

Claims (file PRVEq_AspisV8R19_M31mul_k1.lean; #print axioms propext/Classical.choice/Quot.sound only; no sorry; maxHeartbeats 200000):
- Item 1 (PCUJ-C11): fresh (4bb3b3f, overflow ON) = gate as function equality for field.M31.mul in AspisV8R19.GuardedFieldSlice (AspisR64Field), ComplexFieldSlice (R65), QuarticFieldSlice (R66); also fresh P and reduce_u64 = gate. The gate guard (self<P, rhs<P) makes it total on U32 x U32; the fast branch equals reduce_u64(a*b) for a,b<P by PCVB_M31.fast_chain (symbolic, from P3b). All three definitions are in the 1707 cone (class EQUALITY_PROVED per PCXH_PROVENANCE.json).
- Item 2: r23_product_u32_bounded (R66) has no frozen counterpart at 4bb3b3f. GATE_ONLY_HELPER: r23_gate proves it equals l * r for all inputs (total). Cleared only through its parent gate CM31.mul / CM31.square; the parents' own fresh = gate equalities are outside this job.
- The PRVEq objects compile against the L187 closure with no name clash.

Remaining: parents CM31.mul/square of the gate (not attempted here).
Target not yet established
