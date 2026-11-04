# NGS carrier binding handoff

Work in progress on codex/cx-carriers-bind-20261105. Target: the SAME TX1-bound
proof/public and TX2 resume carriers are equal OR the existing ARX recorded
collision event at Q+2965 occurs. No new collision allowance is authorized.

The source audit located ARX_LocalCharge.binding -> P2P_Charge.binding_or_collision
-> Hiq_JointBinding.binding_or_collision. Its four byte audit reads are already
inside the charged account recorder. Required next: derive the exact packet
carrier association and header match, compile focused modules, compose with
NGR persistence and NGK combined imports, raw ax2 audit and NFX coherence scan.

Native TX1:186 and TX2 authenticated/common producers remain OPEN. This job
proves only their named packet-output implication; it will not invent native
acceptance, assume proof/public equality, change the game, or certify ELF
realization. No shipped code, sibling worktree, key, Kani or extraction changes.
Budget: 0/50 Lean scopes used; Kani/extraction forbidden. Retained trust includes
P6/D188 option-A semantic transport, std/allocator/SDK/ABI/compiler/source-to-ELF,
RuntimePersistence, digest/H realization, RuntimeReturnData, RuntimeMemcmp,
RuntimeClockSlotBinding and the existing cryptographic assumptions.
