# Primitive source reification

Checked: `SdkC_Source.installed_digest` derives the exact op43 return from
D188's existing digestSource equality. `digest_trace` records the one actual
partial syscall and its actual return. `associated`, `consistent`, and
`prefix_preserved` prove source-result association, success-conditioned ROM
reply consistency, and prefix retention for effect syntax. Failure/divergence
attempts retain their prior log and the attempted syscall; no totality added.

This is a local source-helper theorem, not the whole SDK child port. It does
not discharge the arbitrary ChildConeJoin premise of Op5T_Final. In particular
an uninstrumented opaque source call must not be assigned an empty hash log.
No cryptographic/trust assumption or predecessor conclusion changed.

Validation: SdkC_001 failed on local elaboration errors; SdkC_002 passed after
source corrections. No timeout/memory kill or unchanged rerun. The latter
compiled `SdkC_Source.lean` in 2.100664535 s, exit0, peak RSS4342140 KiB,
swap0, exact6G/8G/swap0/tasks64 scope and -M7000. Source revision db2f0170c4
with new module dirty, exact hash/command/direct dependencies in receipt.
All seven new theorem audits report only propext, Classical.choice, Quot.sound.
Failed attempt diagnostics/snapshots remain evidence and are not proof credit.
Used2/100 Lean,0/40 Kani. No shipped file or release artifact changed.

Next: instantiate this source execution at installed leaf and parent bodies;
then compose chronological body calls before applying global recovery.
