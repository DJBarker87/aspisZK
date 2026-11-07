# LIBB modules12–13 handoff after (bq) clarification

Modules12 and13 are DONE under the merged returned-observation gate. The security target remains not yet established; no ledger row credit is claimed. Branch codex/cx-libb-20261107. Stage commits:7b538c7fb2b (module12 gate),9bd362bc8d1 (module13 V0-star). Modules6–11 and all previously proved source modules are unchanged. Only LIBB_ files and own evidence changed; no push.

## Exact claim

LIBB_ReturnFunctional.ReturnFunctional says that at each fixed Env, any two admitted observations whose exits are ret are equal as entire Obs records: returned Ok/Err value AND ordered events. It places no restriction on abort/diverge arms. LIBB_Tx2AuthGate.returnFunctional proves this for the FULL LIBB_Tx2Auth.law at every byte argument, hence on the original Dom064. This discharges the merged C3-BIN (bq) clarification; strict Spec.Functional is neither required nor claimed.

The proof is symbolic. LIBB_ReturnTrace proves a compositional source-log invariant. LIBB_ReturnRun.run follows visible constructors of NJU_CommonObserved.run without unfolding children: a returned parent has no failed Merkle event. LIBB_ReturnObservation.pieces/common/resolved show that every returned observation therefore has the exact deterministic source events; independent stopped outer arms cannot return. LIBB_Tx2AuthGate.returned_resolved proves equality with the resolved graph, including events. Stopped prefixes remain in the full law.

LIBB_V2Star.library is definitionally the existing LIBB_V2Lib.library, with the same VErr/debug/Root0/tx2auth. LIBB_V2Star.gate states ReturnFunctional on Dom064; values supplies the existing NND_Tx2Values.Values. LIBB_V2Star.weak is TAS.lib of this SAME V0 with Root0=True and the UNCHANGED NNC_ObservedLaw.w. weak_identity/weak_exact and canonical_identity compile. No native witness, renderer or free Ops is chosen.

The canonical source/native fold LIBB_Tx2Auth.native is reused unchanged from NMN_064.root and NLT_CompleteRoot.root at SAME original inputs, four original own-input clauses, original outcomes and ordered trace. It covers parse errors/divergence, resolved outcomes and all named independent C04 prefixes, with no suffix invented after a stop. LIBB_RecordRender and LIBB_EnvValues remain reused. Fallible reservations read the original Env.reservation at reached sites; no success arm is fixed.

## Boundaries and assumptions

Discharged: the remaining module12 returned-OBS gate, and module13 admission on that basis. No domain, caller clause, specification, trust row, frozen source or security metric changes. The clarification is the lead's interpretation of the frozen gate, not a silent weakening by this worker.

Retained: original runtime/std/tool/extraction and source-to-ELF boundaries. Bound064 identifies Env.reservation with the SAME reached native record calls as representation. Integration owns I.f064, actual EnvRep and TAS Refines064 installation. The library proves its source/native fold; it does not select the host execution. Headline remains RPx_Deployed.deployed, frozen3, L154 parameter, narrowed D188,100-bit PER-ATTEMPT, privacy and two transactions.

## Validation and reuse

Current run continues the SAME200-scope authorization (L301–L500),0 Kani,0 extraction. Final scope/axiom/resource data:LIBB_GATE_VALIDATION.json; one-line transcript:LIBB_GATE_TRANSCRIPT.tsv. Prior24 scopes and40 raw own-root audits remain historical in LIBB_RESUME_VALIDATION.json. Fresh audits cover all18 new theorems (proof214–218), with raw ax2 and #print axioms agreeing and only propext/Classical.choice/Quot.sound. Failed/stopped proof attempts are excluded and retained; broad search was retired and replaced with source-constructor dispatch. No cap or timeout increase or unchanged killed-job rerun.

L344 is the final focused coherent import:LIBB_GATE_IMPORT imports LIBB_RESUME_IMPORT (merged LIB_BUNDLE_IMPORT and ledger25/LIBB combined closure) plus LIBB_V2Star, checks actual gate/Values/TX1 types and prints actual new statements. Cached unchanged dependencies are reused; no full frozen-release rebuild is claimed. All new proofs compiled smallest-first. Every scope has fresh host count<6,free disk≥40GB,admission exit0 AND allowed:true,6G/8G/swap0/tasks64 and Lean-M7000. Full source/dependency/tool/revision/exit/wall/RSS/swap receipts accompany each.

LIBB_EXPORT.json and LIBB_GATE_PINS.json.xz record retained own objects and rechecked selected dependency/Aeneas hashes; existing exports are never overwritten with changed objects. No cache/key deletion. No shipped-source change or ELF rebuild trigger; inherited artifact pins are unchanged, not newly rebuilt:default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4;devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299;Pool e0e49c344d35575116c0359450315ea4334bfb03006551727f67c04a8cfe09dc.
