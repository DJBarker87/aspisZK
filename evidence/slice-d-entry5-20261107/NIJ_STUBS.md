# NIJ stubs and domains

| Stub family | Lean law | Domain / status |
|---|---|---|
| writer_parse/semantic/transcript/relation/merkle/query/checkpoint/allocation | NIJ_FormatterPackets.string_log, decoded_bytes; retained NHY_StringAppend.contents/literal_frame | Actual String receiver used as LOCAL chronological two-byte log, never a global/static or fake pointer. Initial empty String, capacity>=2; prefix then the fixed deployed label. K005..021 with per-label failures and Parse stability. Encoding law proved; semantic substitution into alloc::fmt::format remains OPEN, so no error row credit. Actual writer byte/growth/drop laws separately K040..055. |
| log_error_* | NIJ_FormatterPackets.abort_prefix, cleanup_frame (conditional local cleanup law) | Syscall argument observation on returned encoded String. Full roots K022/K039 time out and are excluded; remaining same-shape labels unlaunched. No native syscall or String-return credit from these stubs. |
| exact KMX_copy_nonoverlapping / KMX_realloc | retained KMX_CopyMeaning and NHY_StringAppend / snapshot frame laws | Exact patch bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67 applied. Matching negative fails in every credited native configuration. No custom copy stub. Decoder producer K056/057 uses exact KMX pointer copy, no semantic callee stub. |

No field multiplication, writable static, Option<fn> value/comparison, stub_verified Result interface or unpaired field arithmetic. Closed decoder uses full explicit error constructors and existing status/validator laws. RuntimeReturnDataClear and RuntimeClockSlotBinding remain accepted by citation; RuntimeCpiReadonlyEntry7 is not used.

## Admitted whole error roots

`arguments_as_str<'a>` returns the explicit Std None constructor, domain ONLY the fixed literal plus one of8 Error values. Paired native real-value certificate NHY_K111/112; formal reference `NIJ_ArgumentMetadata.image`, theorems `capacity/as_str_none/choose`. No generic Arguments/std-body theorem is claimed. Native wrong-stub control NIJ_K109 returns Some(corrupted) and fails at the actual log argument. Every returning caller establishes this domain by its exact source literal and exhaustive Error constructors.

`log_error_<label>` checks the exact real String bytes at sol_log and returns unit unchanged; paired NIJ_ErrorJoin.bytes/source/exhaustive/abort_prefix. Full actual writer roots70..86 matched per label; no writer stub selected there. Runtime logging/allocator abort interpretations remain existing trust, no value modeled.

`free_cleanup_<label>` logs exact actual dealloc pointer/layout/live contents, with cap18 or36, align1. Native87..102 matched failures. Paired `NIJ_StringCleanup.outside/inside/account_frame/growth_frame` under the existing fresh private-allocation/deallocation primitive. These observers do not implement deallocation; actual Drop/dealloc also execute in the separate whole roots. No account/key argument or unreported account write.

## Final selection clarification

The initial local writer/log models above are historical support, not the stubs selected for admitted error roots. Selected error cut is ONLY calibrated as_str None plus byte-checking syscall observers; real String writer/grow/drop execute. No field multiplication or stub_verified is selected in active-at; actual pure Bool body and helper run. Opposite typed receiver is excluded, not stubbed. K069 unpaired format-return and K120 unpaired SDK rejection remain uncredited.

Active-at native reuse is DENIED: NCF positive receipts remain K-3 suspended; absence of a selected stub_verified does not restore them. Canonical Lean equality/support only.
