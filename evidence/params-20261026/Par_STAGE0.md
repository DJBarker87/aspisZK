# Parameter specialisation, stage 0

Branch codex/cx-params-20261026. Only new Par_ modules and Par_ evidence.
Read root Security and proof discipline, common/local rules, S2 handoff,
plan, diagnosis, interface and adopted route B addendum (the requested S2
paths resolve under docs/research/100bit-spend-path-20261013).

Targets: L085–087, L151–153 by owner-authorised specialisation. Frozen model
SelectedTranscriptParams.params: M = bounded Bytes, Cv = WideExact,
N = 131072, D = 3717, rounds = 33. Reuse the ORIGINAL encoder/decoder and
model LinearMaps. Derive public bound from installed accepted cut length1880.
No new source-to-model correspondence or other cone closure is claimed.

Before: DrvC_NativePair/Nonvacuity retain arbitrary M,Cv,N,p, with p's three
Prop fields. DrvC headline already uses the selected frozen model internally.
After planned: specialise native theorem to SelectedTranscriptParams.params;
construct public Input from SAME accepted pair without public proof binder;
prove laws directly for R1FinalSoundness.SourceInputs.data; export an installed
headline composition without adding any compatibility/security hypotheses.

Budget 0/40 Lean (dependencies count), 0/0 Kani. No replay. Host workspace
/home/dombarker/project-offloads/codex-cx-sound-int2-20261025 and unchanged
S2W launchers. Preflight: only init.scope running. One own 8GiB scope at a
time, MemoryHigh6G/MemoryMax8G/Swap0/Tasks64, -j1 -M7000. Every new top theorem
will print axioms. No infrastructure or shipped-file edits. Historical ELF
pins retained; no rebuild trigger. No key operations or foreign worktree writes.
