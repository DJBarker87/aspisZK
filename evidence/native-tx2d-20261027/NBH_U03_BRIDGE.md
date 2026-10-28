# NBH_U03 — OPEN

Unit is OPEN; local CLOSED members below do not imply enclosing codec closure. No headline premise removed.

The native afterstate and live validators are now CLOSED: NBH_VALIDATORS_BRIDGE.md, K002–K005, L004/L005/L007/L014–L018. The remaining mutable stores/decoder branches and their enclosing Result associations remain OPEN. Existing S2K source-helper theorems are inherited model facts; they do not replace a native loop/store bridge. Preserve failure-path output mutations in live/late encoders. NBD_Dep_DigestDecode/Encode and NBD_Dep_FixedSlice remain explicit lower dependencies.

Exact domains/layouts and EVERY frozen branch are indexed by NBD_LAYOUTS.md and retained in NBD_FROZEN_MEMBERS.md; hashes/cohort names are NBD_MEMBERS.json. Named required U00–U02 statements: NBD_DEPENDENCIES.md. No unmerged NBC result is assumed (NBD_NBC_STATUS.json).

| Exact member | Status | Evidence / exact missing obligation |
|---|---|---|
| `crates/aspis-statement/src/pool_v1/pair_terminal.rs::decode_pool_v1_pair_verified_afterstate_v1` | OPEN | Full native/cohort Result-and-carrier association for this exact member, on the caller-established domain including all rejection branches and mutable output framing; no passing enclosing bridge is delivered. |
| `crates/aspis-statement/src/pool_v1/pair_terminal.rs::encode_pool_v1_pair_verified_afterstate_v1` | OPEN | Full native/cohort Result-and-carrier association for this exact member, on the caller-established domain including all rejection branches and mutable output framing; no passing enclosing bridge is delivered. |
| `crates/aspis-statement/src/pool_v1/pair_terminal.rs::exact` | CLOSED on all reached8/32 specializations | NBH_EXACT_BRIDGE.md; K006/K007, L021, complete static caller-domain inventory. |
| `crates/aspis-statement/src/pool_v1/pair_terminal.rs::validate_verified_afterstate` | CLOSED locally | NBH_VALIDATORS_BRIDGE.md; exact full Result on every typed record and raw limb. |
| `crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::digest_is_canonical` | CLOSED locally | NBD_DigestTrace.native_result / NBD_DigestNativeStep.source / NBD_K006 |
| `crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::encode_pool_v1_pair_late_public_statement_v1` | OPEN | Full native/cohort Result-and-carrier association for this exact member, on the caller-established domain including all rejection branches and mutable output framing; no passing enclosing bridge is delivered. |
| `crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::encode_pool_v1_pair_live_snapshot_v1` | OPEN | Full native/cohort Result-and-carrier association for this exact member, on the caller-established domain including all rejection branches and mutable output framing; no passing enclosing bridge is delivered. |
| `crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::validate_pool_v1_pair_live_snapshot_v1` | CLOSED locally | NBH_VALIDATORS_BRIDGE.md; exact full Result on every typed record and raw limb. |

Retained: P6/runtime/TrustedStd library interpretation, frozen3, narrowed D188, L154 parameter, RuntimePersistence and all original headline hypotheses. No crypto/security assumption discharged, added or weakened. Five total local member bridges are delivered across these three units; all other members are explicitly OPEN, not inferred from fixtures or helper names.
