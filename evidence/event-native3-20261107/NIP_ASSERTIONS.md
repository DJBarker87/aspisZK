# Exact assertion targets and site audit

All five are OPEN. No Kani assertion has been certified. Source revision and
frozen tree identities are in NIP_SOURCE_CENSUS.json. The `physical` argument
is not bound to a concrete native exporter by the supplied NIN inputs.

Let `v = eval H (ART_PartialAccount.account cfg hashv copy allocator
CPH_Program.verifier a)` and `p = eval H physical`, for the SAME configuration,
adversary and H used in NIN_ObserverPredicates.lean. The native producer must
establish these equations, without choosing a new physical projection:

| Predicate | Required native exporter assertion | Inspected frozen native boundary |
| --- | --- | --- |
| OuterTrace | `p.1 = v.1` for every H, full charged chronology including repetitions and rejecting/abort prefixes | lib.rs:13–14 digest forwards `hashv(parts).to_bytes()`; no local exporter-record parameter or outer-log append. lib.rs:36–39 release phase observer returns None. Source cut/order/frame producer is still required; NIF's dots and accumulation association is a dependency here. |
| AdmittedSupport | `p.2.isSome = true ↔ Nonempty (ARU_Support.At ... H)` | lib.rs:61 route check calls pool_route.rs:3–5 `admitted`, which tests instruction bytes only. It is not the bank/two-entry/native-result/persistence/query-agreement support criterion. There is no native optional joint record gated by that criterion. |
| NestedEvents | `p.2 = some run → run.1 = v.1` | The same digest/phase observer boundary has no nested occurrence-record assignment. NIF dots/accumulation SAME-context frame/push association is needed if one first proves a complete outer log; it does not provide an exporter copying that log. |
| CanonicalInput | `p.2 = some run → run.2.1 = F3T_Canon.canonInput (F3T_ByteCarrier.input cfg (submitted v.2.1))` | first_decoded at lib.rs:49–50 passes original public/proof slices to TX1. No native joint record stores the four-component canonical model input. NIN canonical_from_initial/stored_public establish model transport only. |
| LiteralFlag | `p.2 = some run → run.2.2 = accepted v.2` | lib.rs:56 entry returns one ProgramResult; owned::stage1/stage2 are separate invocations. No native joint record retains both wrapper Results. emit_result at r1_pool_adapter.rs:923–942 emits the 792-byte terminal statement result, not a BOTH-Result game flag. NIN accepted_iff/flag_from_results retain the exact missing exporter equation. |

These are universal experiment assertions, not assertions just about successful
fixtures. A local Kani record invented in a harness would prove a new producer,
not any of these native-site associations. No such substitute is used.

The native Rust driver and its extraction are distinct from the external
experiment observer. The latter may be ghost instrumentation; it still needs
an exact pinned implementation/erasure/association to the SAME execution.
The lack of a shipped mutable log alone is not a requirement to modify production.
No whole-program nonexistence claim is inferred from a keyword search.
