# Final native stage

**60/60 Kani invocations PASS. Native allowance exhausted: no further prover command is run.** Lean48/100 attempts (29 passing,19 retained rejections/inspections); the final changed audit is L048. Metadata preflights are60 separate serial capped jobs, not Kani proof runs. Every preflight resolves the exact frozen package/edge graph and active lock; every post-run active lock hash is unchanged. No LPb standalone-lock native proof is credited. No new native timeout, memory kill, failed assertion, cap/timeout increase or unchanged rerun occurred.

- K001-K020: ASJA positions0..19, arbitrary688-byte pre-state,32 source bytes and complete indexed output/frame.
- K021-K040: live positions0..19, arbitrary800-byte pre-state,32 source bytes and complete indexed output/frame.
- K041: ASF8 projected ordered binding/lane prefix (every32-byte binding and lane byte); prefix continuation remains OPEN. Pair with NBK_StatementPrefix on SAME common projection from NBD.
- K042: exact typed ASF8 late[144..1664] length1520 and payment[1664..1880] length216, actual pointer offsets; live deployment domain[256..288]. This checks layouts; it is not an owner/PDA authentication claim or a repaired fixture.
- K043-K050: ONE actual master sequence-decoder iteration specialized per lane0..7 on arbitrary384 source bytes and arbitrary8-u64 pre-state. Exact little-endian word and every other-row frame. No complete decoder or adopted op48 association is claimed.
- K051-K058: corresponding192-byte Pool checkpoint iterations, including the post-store capacity predicate with exact >2^20 boundary and mutation before local error. No1768-byte verifier checkpoint association is implied.
- K059: native ASJA fixed header/index/root byte cut, full returned688-byte image before frontier. SAME root32-byte result is an explicit OPEN DigestEncode child cut.
- K060: native live std fill/header/pool/domain/sequence/index/root cut on arbitrary800-byte pre-state; full indexed image before frontier. Symbolic model fill is independently proved by NBK_Fill and all20 source frontier iterations by NBK_LiveBytes. No native frontier loop is unrolled. SAME encoded root child remains OPEN.

No new Kani stub. Cut bytes are not independently assumed successful child outputs. The source row loops are split into one native iteration by fixed position and model induction; no whole frontier/sequence loop is submitted. Native sequence fragments still need their SAME adopted-carrier induction/association, expressly OPEN in the unit tables.

Frozen Rust source4bb3b3f5, Kani0.67.0, offline opt-level3, scopes MemoryHigh6G/Max8G/Swap0/Tasks64, one at a time. Full AGENTS6 metrics and source/dependency/tool pins are in NBK_ATTEMPTS.jsonl and individual receipts; `#print axioms` is N/A for Kani. Model audit prints standard axioms only. No claim of a coherent full release replay or source-to-ELF discharge.
