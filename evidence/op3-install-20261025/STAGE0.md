# TX1 op3 installation preflight

Scope: only first source-operation connection, TX1 parse_shape. Branch
codex/cx-op3-install-20261025; initial revision 4dfb9dccec5ce1289c8cabe88b125e6378fd5aea.
Read root AGENTS.md including Security and proof discipline, common/local rules,
S2 ownership/plan/diagnosis/interface (historical paths under
 docs/research/100bit-spend-path-20261013), C3-BIN 2026-10-23 01:20,
row-shape and row-order handoffs/modules, SOUND-INT and SInt2 composition.

The installed dictionary preserves arbitrary op3. Actual candidate.rs:40 checks
length 57607, magic R1P3CB18, tag2, zero bytes9..16. The frozen header component
is OraclePortHeader.accepts, used in OraclePortCompactDraft.parse and then
OraclePortStoredParserC4.parseReached. No observed disagreement at inspection.
An existing extraction exists as Stage2ContinuationParse (explicit std-operation
ports); investigate concrete port installation before claiming source binding.

Host read-only preflight: approved coherent SInt2 workspace reachable; no populated
build scope besides init.scope. Reuse objects and unchanged launchers; every
attempt gets -M7000, 6G high /8G max /swap0 /tasks64. Budget 0/60 Lean,0/20 Kani.
No formal result: exit,wall,RSS,swap,axioms inapplicable to this inspection.
No premise discharged or added. No source/model/security-contract change.
Only Op3I_ new modules and this evidence directory may change. No keys, shipped
files or other workers' sources touched. No ELF rebuild trigger; inherited pins
f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4,
63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299,
121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548
are not freshly reproduced. Target not yet established.
