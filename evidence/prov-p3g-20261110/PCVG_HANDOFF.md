# PCVG_ HANDOFF: phase P3g

Target not yet established. No ledger row, trust row, RSL, contract or shipped source changed; no row added (text drafted only). 0 Lean and 0 extraction host scopes used (the host was unreachable at first; once reachable the session context went to the lead's re-scoped items A, B, C).

Done: (A) PCVG_TRUST_ROWS.md, HM-C/D/F/G drafts in the HM-A/HM-B form, with the HM-G caveat that read_discriminant on Aspis enums may be an Aspis-side proof item (lead to decide). (B) PCVG_EXTERNALS_BY_CRATE.json: 99 unresolved externals, 68 aspis-frozen (41 distinct names, open obligations), 16 solana (into HM-A; `solana_sdk_ids.bpf_loader_upgradeable.id` is not named in HM-A today), 15 core/alloc/std (14 into HM-D, 1 into HM-F). (C) PCVG_DIFFCHECK_HMF.json: count_ones and trailing_zeros EQUAL on all 65536 u16 inputs (local; rustc 1.93.0 not the pinned sysroot). HM-C, HM-D, HM-G have no differential check.
Triage: PCVG_REMAINING.json. WideToBytes x4 -> DEPENDS_ON_LIBRARY_TRUST (HM-B). S1NativeCompact expand_semantic x3 read from the gate: needs the Ops-bound shape plus row_shape by cases, type alias and Result-wrapper constants; no numeric difference seen. Rest not attempted.
Tools: PCVG_run.py (copy of PCVF_run2.py, renamed, host base codex-pc-prov-p3g-20261110, not yet used).
