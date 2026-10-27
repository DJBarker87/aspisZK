# Dependency rebuild and full kernel audit

Original missing objects: **92 → 0**, each rebuilt with a charged attempt.
All 92 sources match pinned research where present (53), or are explicitly
identified unmerged branch additions (39). These source origins are retained
in resume5-plan.json; no claim is made that the 39 unmerged additions already
exist on research. The physical and provenance inventories remain separate.

Two additional extraction modules were rebuilt from pinned research bytes,
replacing the restored cache's older anonymous-discriminant variants:
R1Z.BuilderAdmissionExtracted (36300) and AspisR1ProverCommit.Types (36301).
The corrected snapshot command copied their previous shared source and object
bytes under the task snapshots/resume5-ID directories before replacement.
This refreshes shared .olean files; subsequent FullAudit imports their current
objects and records the precise dependency hashes. No foreign worktree or
existing proof source in this worktree was edited.

Full kernel target: **R1Z/PV_Src_FinalAudit, 36302, exit 0**.
129 PV_Src modules, 575/575 printed axiom sets, every set a subset of
{propext, Classical.choice, Quot.sound}. Wall 2.20 s, peak RSS 4,234,376 KiB,
swap 0; source revision 9b3806cc36. Complete raw output: out-36302.log; source
SHA, import-object hashes and full axiom lines: resume5-attempts.jsonl.
The loaded closure has no missing import object (Lean completed its import
and all requested checks). This is not, by itself, every imported object's
source/byte provenance attestation. Post-build cross-root source/object
inventory: resume5-stage1-full-closure.json. Literal source availability on
unmerged research and archived source alternatives remain visible; merge
approval belongs to the lead. No endpoint premise was discharged by this replay.

95/100 authorized Lean attempts consumed at this stage, all successful.
No Kani attempt has been charged. No unchanged full regression was repeated.

Post-build expanded inventory: 836 project modules plus 193 external import
roots; **zero missing enumerated objects**. All 775 project modules with an
existing selected research source match its pinned bytes. Sixty original
branch additions plus the new audit source do not yet exist on research; no
existing research source mismatch remains in this source selection. Fourteen
modules have differing archive candidates recorded rather than silently hidden.
The literal pre-merge research-HEAD/package provenance gate is **not claimed
passed** (resume5-stage1-gate.json); kernel audit PASS and byte-gate approval are
reported separately.
