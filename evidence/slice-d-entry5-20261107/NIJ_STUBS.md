# NIJ stubs and domains

| Stub family | Lean law | Domain / status |
|---|---|---|
| writer_parse/semantic/transcript/relation/merkle/query/checkpoint/allocation | NIJ_FormatterPackets.string_log, decoded_bytes; retained NHY_StringAppend.contents/literal_frame | Actual String receiver used as LOCAL chronological two-byte log, never a global/static or fake pointer. Initial empty String, capacity>=2; prefix then the fixed deployed label. K005..021 with per-label failures and Parse stability. Encoding law proved; semantic substitution into alloc::fmt::format remains OPEN, so no error row credit. Actual writer byte/growth/drop laws separately K040..055. |
| log_error_* | NIJ_FormatterPackets.abort_prefix, cleanup_frame (conditional local cleanup law) | Syscall argument observation on returned encoded String. Full roots K022/K039 time out and are excluded; remaining same-shape labels unlaunched. No native syscall or String-return credit from these stubs. |
| exact KMX_copy_nonoverlapping / KMX_realloc | retained KMX_CopyMeaning and NHY_StringAppend / snapshot frame laws | Exact patch bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67 applied. Matching negative fails in every credited native configuration. No custom copy stub. Decoder producer K056/057 uses exact KMX pointer copy, no semantic callee stub. |

No field multiplication, writable static, Option<fn> value/comparison, stub_verified Result interface or unpaired field arithmetic. Closed decoder uses full explicit error constructors and existing status/validator laws. RuntimeReturnDataClear and RuntimeClockSlotBinding remain accepted by citation; RuntimeCpiReadonlyEntry7 is not used.
