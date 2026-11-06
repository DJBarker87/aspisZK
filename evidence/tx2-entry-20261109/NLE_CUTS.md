# NLE native cut inventory

No native result in this packet is a complete row root.

| Attempts | Shape | Outcome / model statement | Exact limit |
|---|---|---|---|
| K004/K005 | Actual whole tx2_authenticated, static buffers, custom Hash, parse reply tied to buffer tag | PASS / intended FAIL | Diagnostic only: correlation, custom deployed carrier and original marker/Option<fn> review. |
| K006 | Actual whole parent, unsafe harness-owned Input recovery, three arbitrary byte coordinates | TIMEOUT90s | Retired; no credit. |
| K007/K008 | Result/descriptors/oracle-state part of K006; independent oracle tags | PASS / intended FAIL | Unsafe recovery and Hash-to-deployed transport unproved; no payload frame or complete child-world packet. |
| K009/K010 | Public-coordinate frame only | PASS / intended FAIL | Same unproved ghost carrier; diagnostic only. |
| K011/K012 | Checkpoint-coordinate frame only | PASS / intended FAIL | Same unproved ghost carrier; diagnostic only. |
| K013 | Proof-coordinate frame only | TIMEOUT90s | Retired; no control/pass credit. |
| K014/K015 | Safe parse segment; explicit local &mut Log; actual program SolanaDigest type; all3variant/8error replies | PASS / intended FAIL; NLE_SafeCuts.ParseCut, NLE_NativeTags.parse_roundtrip/parse_domain | Reviewed segment/transcription support, fixed1880/57607/1768 inputs. Does NOT establish payload identity, native arbitrary-world interpretation or the complete frozen parent association. |
| K016/K017 | Safe common-tail segment; same local record/type; Ok and all8errors | PASS / intended FAIL; NLE_SafeCuts.CommonCut, NLE_NativeTags.common_roundtrip/common_domain | Same metadata-only/segment scope. Complete065 packet and physical association remain. |

Safe segment source is committed only as NLE_auth_steps.patch. The original frozen source is pinned at4bb3b3f51e16b4525f1d10336e2b0bcbbd775387: candidate.rs:328 `parse_shape(proof)?;` and:330 `tx2_common(public_bytes, proof, checkpoint, hash, obs)`. Oracle instrumentation carries the callee reply and log as explicit additional local parameters. The retained caller fields are public/proof/checkpoint and deployed digest. Marker None is supplied by the emitted source/NEF release pin; the safe native segments contain no Option<fn> value assertion.

The assertion predicates deliberately mention metadata only. `Descriptor.base` equality is not a theorem about bytes or provenance. The native selected input domain is recorded, not widened to arbitrary callers. The source scope builder NLE_CallerScope derives the numerical clauses from SAME snapshot reads/range and actual encoder Array; installing these values into the native physical carrier remains a separate obligation. No standalone native credit is proposed before that association and the exact OPEN-child packet statements are available.

Exact KMX patch hash, resolved full feature tables, frozen-graph comparison, source-erasure checks, post-run lock hashes, commands, revisions, exit, wall/RSS/swap and controls are in per-attempt receipts and NLE_NATIVE_POLICY.json. No proof_for_contract/stub_verified shape is used. No field multiplication is proved or stubbed; no extraction occurs. Marker stubbing in the unsafe diagnostics is paired only on the source None domain with NLE_AuthScope.mark_stub_domain; it does not repair their provenance gap.
