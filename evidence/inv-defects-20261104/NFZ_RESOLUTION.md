# NFZ part-3 resolution

**INCOMPLETE.** Frozen Rust 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387; sha256-pinned NFX baseline. No reviewed entry edge, new row, exclusion or status change is claimed.

## Exact identity and partial compiler authority

field/wide_exact.rs defines WideExact and its inherent from_qm31. There is no inherent from_m31 there. scalar.rs imports that same type and implements CodeField::from_m31 at lines 87–91. TX2:046 names that single trait method, not a second WideExact type.

NFZ_CORE_MIR_REVIEW.json pins successful core MIR diagnostics. The two MIR flag sets (-Zmir-opt-level=1 and =0) in B003 independently agree on these conditional bodies:

* scalar.rs:87 WideExact embedding calls the QM31 trait embedding then inherent WideExact::from_qm31.
* scalar.rs:70 QM31 embedding calls the CM31 trait embedding then inherent QM31::from_cm31.
* scalar.rs:56 CM31 embedding calls the M31 trait embedding then inherent CM31::from_m31.
* scalar.rs:41 M31 embedding reduces its raw limb modulo P and constructs M31; it has no local function callee.

Six candidate records (C0001, C0035–C0039; C0001/C0039 repeat one site) therefore have compiler-confirmed target identities. Their entry reachability remains unknown. Caller MIR was not emitted for the verifier/program, so this job cannot admit the WideExact caller or first_decoded callback edges. Neither an optimized no-op trace nor source aliases alone license a reachability exclusion.

## All 39 candidates

NFZ_CANDIDATES.json retains every candidate and its explicit part-2 disposition. C0003–C0024 are the 22 concrete E::from_m31 calls in Transcript<H>::queries; C0025 is accumulate_batched_with_node's embedding. C0026–C0031 are Weights::new's unresolved method-chain candidates. C0032 is external_local_packed_raw's map(extension_limbs). C0033 is first_decoded's map_err(error); C0034 is the source-cfg-disabled legacy callback. C0002 is circle_sample's fallback closure. The remaining six are the conditional core embedding identities above. None has compiler-certified entry reachability; all remain OPEN review obligations.

The four absent functions are M31/CM31/QM31 trait embeddings and circle_fallback_point. If reached, add OPEN transaction occurrences and recursively include their callees. Do not force the total to stay 587. In particular, do not confuse the three missing trait embeddings with existing inherent constructor rows.

## Q caller packet obligation, without downgrading

The prospective Q finding is the missing accumulate_batched_with_node → scalar.rs WideExact::from_m31 inventory edge. Its actual native caller certificate runs the real body, as the lead rules. The NFS model already names and models this callee: NFS_NEV_AccumulateRaw_Funs.lean invokes it; NFS_NEV_AccumulateRaw_FunsExternal.lean forwards to NEV_CodeFieldRaw; NFS_NEV_AccumulateCallees.from_m31 proves equality to (NBF_RowInstall.install ops).op10 for m.val < 2147483647. NFS_NEV_AccumPacket.result_state_effects covers the complete modeled accumulation Result/state/effects on its input Domain through NFS_NEV_AccumulateComplete.reference. These are existing statements, inspected read-only, not new Lean credit or a proof that the inventory repair is complete. The lead must assess the explicit call-domain and new-row packet obligations when caller evidence is available.

NFM_CLOSED.json claims four_dots_one/four_dots only; it does not claim this embedding or Transcript::queries. No NFS_CLOSED query packet directly closes Transcript::queries. Its embedding obligation must be named by its own caller packet. All historical row statuses are preserved; no downgrade is made here.

## Attempts and failure provenance

B001 remains intact. New attempts ran one at a time with fresh allowed=true/exit-0 admission and MemoryHigh=6G, MemoryMax=8G, SwapMax=0, TasksMax=64; all swaps zero. No timeout, memory kill, cap increase, Kani, extraction, Lean or ELF rebuild occurred.

| Attempt | Exit | Wall s | Peak child RSS KiB | Result |
|---|---:|---:|---:|---|
| B002 | 101 | 0.929 | 137104 | Corrected dependency projection passed; rustc helper-thread EAGAIN |
| B004 spare | 101 | 25.055 | 771672 | Four-CPU/thread repair worked; core diagnostics passed; statement missing include |
| B003 independent | 101 | 11.727 | 545104 | Core MIR opt 0/1 and typed HIR passed; same missing include stopped caller diagnostics |

B003 was submitted after my local include collector failed on a binary include: the shell command failed to stop on that nonzero preflight. This is my own input/fail-fast error. Its original inputs and failures are retained. The final collector supports binary files and follows literal includes transitively; NFZ_host.py now checks that generator before admission and refuses retained attempt IDs. NFZ_PAYLOAD_PREFLIGHT.json checks every byte against frozen Git objects. This final repair is unsubmitted; all three scopes are spent.

Source and frozen Cargo.lock were checked before/after the attempted Cargo checks; the lock remains 5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef. Resolved deployed features and package graph are in NFZ_METADATA.json.xz and NFZ_GRAPH_CHECK.json; exact commands/tools/source pins and section-6 metrics are retained per attempt. #print axioms is N/A: no new theorem. The scratch target is a debug type-check dependency build, never an arithmetic gate.

## Claim boundary

NFZ_inventory.py reapplies the empty blocked overlay and NFZ_slice_build.py regenerates Q/S/D. The ledger remains byte-equivalent in content to NFX. Independent authority exists only for the conditional core bodies, not the complete overlay. Runtime/security trust is unchanged; D188 trace fidelity and L187 remain open. Headline AspisR1.RPx_Deployed.deployed, L154 statement parameter and 100-bit PER-ATTEMPT target are unchanged; target not yet established.

## Part 3 terminal result

B005 failed for my own wrapper reason after successful verifier-library MIR emission: libc probes rustc from a Cargo build script whose environment omits RUSTFLAGS; NFZ_rustc.py:7 raised KeyError. The explicit lead stop applies: B006 unused, no repair rerun or independent scope. Peak17 threads,25.118775121169165s,751856KiB,swap0; stable1.94.1, one Cargo job/-j1/codegen unit and jobserver token. All495 source pins and lock unchanged. NFZ_B005_FAILURE.md and NFZ_REMAINING.md record exact failure and corrected unexecuted command. All39 candidate entry reviews remain pending; no edge, row, status, exclusion or security credit. Closure regeneration still585/587. The part2 sections above are historical; their “unsubmitted final payload” statement is superseded by the successful part3 preflight/staging and the terminal B005 attempt.
