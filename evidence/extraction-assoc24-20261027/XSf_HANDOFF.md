# XSf handoff

Target not yet established. Branch codex/cx-extraction-assoc24-20261027; base dd85daba6ee988014e0eb5066cdd905ba3264b99. All work is confined to XSf modules and this evidence directory. No push, merge, shipped/cfg(kani) edit, other worktree edit, key or wallet operation.

## Exact A2 result

A2 CLOSED on the actual reached wide_view/prepare domain: XSf_Closed.prepare (L018; final audit L102).

```lean
∀ {H : Type} (D : C.D H) (sem : C.Sem H)
  (proof semantic y1 : Slice U8) (hash : H) (old : Array C.E 29#usize),
  mapR (fun (p : core.result.Result E.Prepared E.Err × Array C.E 29#usize) =>
    (inner cprepared ce p.1,p.2)) (XSf_Closed.narrowed D sem proof semantic y1 hash old) =
  XSf_Closed.installed D sem proof semantic y1 hash old
```

Both wrappers in XSf_Closed.lean include the SAME actual cohort wide_view call, all its failures, and the entire prepare continuation. narrowed uses XRy_NarrowPrepare with the CLOSED LPk low replacement; installed uses PreparedScratchModel.prepare XRo_Join_Installed.actual and the same cview. The theorem has no canonicality, successful-prepare, selected-output or whole-claim law premise. SAME reached parser derives inactive bounds; SAME gamma call derives canonical powersPublic29 scratch; SAME ordinary kappa derives its bounds. XSa_CachedClaim.claim then substitutes the whole claim in both fold branches. All checked XSa/XRy/XRw/XRv/XRt/XRs/XRq results are reused; arithmetic is not re-proved. XSf_DEPENDENCIES.json lists the complete selected import closure and CLOSED leaf packet references; XSf_DEPENDENCY_CLOSURE.json pins every selected object, source/receipt/import provenance and inherited coherent-cache manifests.

Domain issue made explicit: arbitrary caller-constructed typed View does not enforce canonical inactive; source serialization is total on noncanonical values (XSf_ParserWitness.serializer_counterexample). No broader unrestricted typed-view equation is claimed. The whole reached-source theorem introduces no caller precondition or weakened cohort failure event. A2 is a local association closure, not headline extraction or native release closure.

## A3 strongest result

XSf_A3Narrowed.trace (L101) starts with the SAME reached wide_view and SAME accepted narrowed prepare and derives ONE LPq_PreparedTrace.Trace on the exact semantic/y1, scratch, inactive and returned kappa. It produces a canonical native-model output, equals that returned claim, identifies the SAME native powers29 array, and proves uniqueness among local traces. All gamma/kappa/inactive/g/semantic/y1 bounds are derived from that producing execution. XSf_PrepareSemantic and XSf_PrepareY1 discharge the two input domains retained in the earlier conditional trace; accepted scalar loops supply their actual reads and byte decodes. Existing LPq native-model arithmetic, powers and weighted folds are imported, not replaced.

A3 remains OPEN: LPs whole native prepared_claim P6 is not merged. This accepted local carrier-trace/model theorem does not prove the frozen Rust whole-body/native-carrier association or full native rejected-path coverage. No new trust, cryptographic premise, game, metric, failure event or release pin is added or changed. Next: import LPs CLOSED native bridge when merged, compose its SAME carriers/results/errors with XSf_A3Narrowed, then finish the remaining association rows. Do not re-prove these checked adapters or discard their persistent objects.

## Headline and exact row statuses

Adopted AspisR1.RPx_Deployed.deployed is unchanged, inherited83T/0P/13G with L154 a statement parameter. Complete before/after kernel statements are retained verbatim in XSf_HEADLINE.json; both SHA2568ae0107f9dbb7374135912ff9dda3597ad0096023d0deed471b0cd4dcf305523. Actual root source equals the job base. Ledger atomic-family/SAME-witness/shared-nonce/L185=L159: removed0/added0/changed0, delta T0/P0/G0/C0. Local canonicality obligations were discharged; no actual headline premise was removed or replaced by a bundle. No fresh absolute recount/root compile/root axioms audit claimed.

A0 OPEN; A1 OPEN; A2 CLOSED on reached wide_view/prepare domain; A3 OPEN; A4 OPEN; A5 OPEN; A6 OPEN; A7 OPEN; A8 OPEN. Exact scopes are in XSf_OBLIGATIONS.md. XSd owns A0/A1/A4/A5; XSe owns A6-A8, untouched. No D188 frozen-release credit is claimed while those rows remain OPEN.

## Validation and budget stop

Mandatory stop: **100/100 actual Lean, 84PASS/16FAIL; Kani0/10**. L004/L006 stopped before Lean for missing input dependencies, not prover results or launcher malfunction; they are excluded from100. The existing unchanged runner resolved these by building the missing unchanged prerequisite once. No Lean process may launch under this allocation. Final L102 audits all41 new theorem roots; only subsets of [propext, Classical.choice, Quot.sound], including two with no axioms. All failed diagnostics/sorryAx prints are retained and excluded. XSf_VERIFICATION.json has zero errors; XSf_AXIOMS_COVERAGE.json has no missing root. No timeout, memory kill, cap increase or unchanged actual compiler rerun.

| Target | Attempt | Exit | Wall seconds | Peak RSS KiB | Swap | Source revision (dirty source hashed in receipt) |
|---|---|---|---|---|---|---|
| XSf_Closed | XSf_L018 | 0 | 1.982771253969986 | 4780292 | 0 | f465affa3a32050b6e843966a9bed82bf01275fd |
| XSf_A3Narrowed | XSf_L101 | 0 | 4.144993413996417 | 5268688 | 0 | 255ed3733ae51153ef1a100edd41840af3541a51 |
| XSf_Audit | XSf_L102 | 0 | 4.3462221850058995 | 5247372 | 0 | 255ed3733ae51153ef1a100edd41840af3541a51 |

Total compiler wall 248.68101394805126s; peak RSS 5297032KiB; swap0. Every compile ran one module in a serial host scope: MemoryHigh6G/MemoryMax8G/MemorySwapMax0/TasksMax64, -j1-M7000, with admission allowed:true AND exit0 as enforced by the unchanged XRy invocation guard. Exact source/dependency/Lean hashes, argv, exit, wall, RSS, swap, cgroup limits and full axiom/error lines are in each receipt/stdout/source snapshot. No build/launcher/admission/monitoring infrastructure was edited. XSf_verify.py is the inherited static receipt checker with its evidence prefix changed; it launches no builds. No Rust, Kani, SBF, full frozen manifest or unrelated unchanged regression ran.

## Non-vacuity and retained cache

XSf_Nonvacuity.powers_and_sum constructs SAME canonical29/7 powers arrays and a successful weighted fold using symbolic one/zero totality. XSf_ParserWitness.parsed_zero/parse_inhabited construct successful32-byte decoding and canonical inactive. Canonicality conditions mention only actual input limbs, not desired output equations. A2 quantifies all source bytes and failures without assuming prepare success. A3 acceptance is explicit. A joint deployed accepted-root witness remains OPEN; no successful release fixture is claimed. XSf_ClaimReturn.UNCOMPILED.lean.txt was never launched and has no credit.

Persistent cache /home/dombarker/project-offloads/codex-cx-assoc-a2-cache-20261027 retained: 196 inherited objects unchanged, 84 additions, 280 final. Additions are59 unchanged prerequisite objects (58 LPq closure adapters including CarrierFacts, plus XRk_ResultTools) and25 XSf objects including final audit. Every object is hashed at start/end; no other cache, shared object directory or existing proof source was written. The initial library directory scan records220 entries; the complete239-path inherited LEAN_PATH Aeneas pin was independently matched after L008, before subsequent work, and is unchanged at end. Do not invent earlier fresh start hashes for omitted library paths. XSf_CACHE_START/AENEAS_START/CACHE_END/CACHE_CHECK preserve exact inventories and timing provenance. Full selected import closure has6791 modules, all resolved, with no inherited object-hash mismatch or unavailable current accepted source.

No shipped change triggered locked-graph/native or three-ELF gates. Historical pins, not freshly reproduced: default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4; devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299; Pool121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.
