# LPm prepared_claim native P6 bridge

**OPEN — local bridges checked; the whole opaque leaf is not closed.** No
headline premise is removed. AspisR1.RPx_Deployed.deployed remains the headline;
L154 is its statement parameter, and narrowed D188 remains the trust boundary.
S2 and the deployed 100-bit security target remain not established.

## Target and pins

Frozen `crates/aspis-r1-cost-probe/src/verifier.rs`, private `prepared_claim`,
revision `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`. Retained cohort:
`AspisR1CurrentPreparedClaim.verifier.prepared_claim` with
`AspisR1S5ClaimDotConcreteAdapter.concreteOps
AspisR1EbyKPushDecodedProductUpdate.QRaw`. Session A candidates are imported
read-only. The coherent SInt2 workspace is reused; 31 missing unchanged
prerequisite modules were privately rebuilt, with full receipts. No second
corpus copy or shared-object modification.

Frozen Cargo.lock SHA256:
`5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef`.
Every Kani run has a fresh offline cargo-metadata graph comparison with the
frozen package/edge graph, and identical before/after lock hashes. Kani 0.67.0
omits its unsupported --locked flag; metadata uses --locked --offline.
LPm_PATCH_AUDIT.json checks every exact per-run source snapshot hash before
retaining its cumulative patch. LPm_SOURCE_AUDIT.json checks all 498 frozen
shipped source/config files locally and normalizes only exact cfg(kani)
registrations in the retained scratch. Tool hashes are in LPm_tools.sha256;
per-attempt receipts record command, source revision/hashes, dependencies,
exit, wall time, peak RSS, swap, cgroup and printed axioms.

## Checked stages

| Stage | Evidence | Exact scope |
|---|---|---|
| Continuing power multiplication | LPi_K015/K016 retained; K009; L054 LPm_PowersBridge.native_result | Actual seven writes and six continuing multiplications on canonical E, with complete eight-word value/return threading. The emitted FIo helper equals the actual returned array via the linked trace. Cohort ClaimPowers owner port remains OPEN. |
| Private Dot update | K010; L055 LPm_PublicState.private_source; L052 LPm_WordFold | Arbitrary four-u64 old/raw carriers, all four wrapping updates/frame; raw value derived from the retained source law, not assumed as a whole output. |
| Public EbyKDot caller | K013; L067 LPm_PublicPort.source | Same actual c0/c1 borrowed Dot, left/right order, all argument words, count and rejection path. Complete native/cohort returned state equality on canonical E/Q and count<4096. K013 also tests arbitrary noncanonical Q and count<29, with zero private calls and unchanged state on rejection. |
| Six public folds | L068/L069/L076/L077/L079 | Local actual push transitions imply the ordered decoded FIELD product sum; no sum-value invariant is supplied. LPm_PointLength.all_six identifies all six cohort loop Results on SAME sem/y1/g, deriving 29 steps from the iterator observations. It still requires the six linked local traces; construction from the entire native caller is OPEN. |
| Finish | L071 LPm_FinishPort.source; inherited LPf_PublicDotAllStates | Total native finalizer and concrete cohort finish return the same eight-word E after the explicit nominal port, for every eight-u64 state. |
| Semantic selections 0–4 | K014; L059 LPm_SemanticSelections | Actual Verified claims/extra/before_z1 carriers, arbitrary coordinate/lane, all five branches; exact cohort routing includes Result failures. K014 uses arbitrary u32 QM31 bytes with valid Rust representation, not zeroed unselected rows. |
| Point 5 native read | K012 | Actual field(y1,l).c0 on arbitrary 928-byte y1, l<29 and canonical selected field; all selected byte/word positions. Cohort ClaimParser field owner port remains OPEN. |
| Weighted arithmetic | L070 LPm_WeightedField.step/trace_value; K016 | Total emitted multiply/add and ordered value induction on canonical E. Native after-multiply add tail independently checks every output word. The native pre-multiply operand/continuation and cohort weighted-sum owner join remain OPEN. |
| Parts initialization/store | K017/K018 | Actual seven-element carrier: parts[0]=inactive, six point+1 stores and complete untouched-word frame, arbitrary row/limb. No whole private-body conclusion follows yet. |

Every installed replacement is paired in LPm_STUBS.md with a total emitted Lean
law and the exact canonical caller domain. Field multiplication is never
proved in Kani; nondeterministic outputs are constrained by the natural-value
specification. L050 proves specification arithmetic bounds. K013's private Dot
stub is paired with L055.private_source and the retained exact raw value law.

## Failed shapes retained

K008 isolated continuing-call value comparison, K011 whole-matrix raw-to-Q
construction, and K015 combined seven-part selection/multiply/add timed out
at the unchanged 90-second limit. They are excluded. K009 splits return
threading with the SAME full natural-spec multiplication stub; K014 changes
the matrix construction to arbitrary representation-valid carrier bytes;
K016 splits after multiplication and checks the native add tail. These are
changed cuts, not unchanged replays. K002 checkpoint timeout is separately
recorded in LPm_checkpoint_LEAF.md. No cap/timeout increase or OOM replay.

Rejected Lean snapshots, diagnostics and sorryAx recovery prints are retained
and excluded. L020 encountered an unchanged missing transitive protocol import;
minimal source imports and private prerequisite rebuilds avoid attributing an
uncompiled protocol closure to this work. L072–L075 rejected source-loop
rewrite shapes; L076 fixes the proof with a local body equality before the
single loop unfolding. L078 rejects nominal Usize/Nat rewrites; L079 fixes the
ports and proves the iterator-derived lengths. Accepted top theorems print only
propext, Classical.choice and Quot.sound (or subsets).

## Exact open stages

1. Port native FIo powers7 to concrete cohort ClaimPowers.powers, preserving
   all seven canonical eight-word carriers. L054 closes only FIo, not this port.
2. Port native point-5 selected-byte field/c0 to cohort ClaimParser.field/c0.
3. Construct the six LPm_PointLoop.Trace values from ONE actual private caller,
   its unchanged semantic carrier, powers g, all 174 reads and actual ranges.
   L079 is a local-trace association, not this universal construction.
4. Join all seven parts with the same k array, native pre-multiply operands,
   the paired field result, add continuation and concrete cohort sum Result.
   K015 is excluded, not credited by the passing add-only tail.
5. Compose initialization, six loops, stores and seven weighted steps into
   ONE native prepared_claim Result and its empty digest-attempt sequence.
   No such whole-body theorem or universal native cut is currently exported.

The expected caller domain must be discharged from the adopted caller:
canonical inactive/kappa/g and checked semantic scalars; y1 length928 and
selected fields canonical; public fold count starts0 and stays below29.
K013 establishes native rejection for noncanonical scalar, but the complete
arbitrary-error prepared_claim association is not claimed.

Repository crates/programs remain byte-identical to frozen release. No ELF
rebuild trigger fired. Retained, not newly reproduced, pins: default
f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4;
devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299;
Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.
Pinned ABI/runtime/compiler/library/source-to-ELF admissions remain; no new
cryptographic assumption, headline premise removal, or security closure.
