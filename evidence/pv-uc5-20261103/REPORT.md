# D577 continuation report — alias-safe final differential running

Branch `codex/pv-uc-20261029`, continuation base `0e8a457c55`; production source fixed at `0e3df6e684`. Final optimized user_client SHA256 **`fc8808eb454f3156dba550140398cc3a74af4c88ee5b3491d2d04d33ee904558`**, 2,031,048 bytes. Privacy target not yet established. No timing experiment, RPC, deployment-wallet access, push, merge or key cleanup.

## Gate results

| Gate | Result and evidence |
|---|---|
| Actual changed-client extraction | PASS N91106 final-source regeneration; N91100 original pinned Charon/accepted ae1-2 Aeneas; entry-extraction-final/receipt.json + reuse-binding.json |
| Optimized final production build | PASS N91108, Rust1.94.1 client profile, locked/offline, deployed feature set; final-build.json |
| Three release ELF identities | PASS N91108 retained-byte hashes against all three frozen pins; original fresh SBF builds N75137/38/39 reused |
| Fixture source/executable identity | PASS, unchanged; executable SHA256 6db76577e5f3331152bbcd6c22739ceea1e0413ed77cf34f10789f4d72488194 |
| Symbolic literal certificates | PASS Lean91000–01,42 distinct short-literal size/bound certificates,68 call occurrences; no decide/native_decide |
| Final entry compilation | PASS Lean91002–06 and91009;22 carrier/105 operation parameters remain explicit |
| Conditional formatter congruence | PASS Lean91011, six theorems ported to the final extraction without weakening hypotheses |
| Full-private NEP raw audit | PASS Lean91097–98: main5280 constants/86613 edges, decoder2224, six formatter roots complete; only standard axioms; nep/summary.json |
| Non-dumpable startup/core limits | PASS N91109 successful finalELF hardening syscalls, finalELF core limits0,0; identical initialize helper PR_GET_DUMPABLE0; runtime-final/summary.json |
| Forced panic/no core | PASS N91109, early and post-wallet-read finalELF SIGABRT, literal stderr, no core file |
| Literal /proc status Dumpable field | UNAVAILABLE on Linux6.8; status has CoreDumping0, which is not asserted to establish non-dumpability; direct prctl/source/syscall evidence above |
| Raw output FD discipline | PASS N91109 rejects stdio, input FD, regular file, read-only pipe, and stdout/stderr/input-pipe aliases; successful212-byte custody awaits full fixture run |
| Final production100-pair public differential | RUNNING N91110; one submission only, public statement/JSON/instruction comparison,200 actual optimized prover calls |
| Complete raw-secret-field file/stdout/stderr search | RUNNING N91110; every key/salt/value/full-record match retained; intentionally public asset word recorded separately |
| Timing | NOT RUN, lead-only named window |
| Full privacy endpoint/deployment closure | NOT ESTABLISHED; no endpoint premise removed |

## Client source and custody

Only wallet.rs, diagnostics.rs and plan.rs change after the continuation base. Source hashes and scope checks are in source-scope.json; every launch also records its committed source inputs. No crates, programs, manifests, locks, fixture code, proof/statement encoding or TX1/TX2 instruction layout changed. The fixture SDK pin remains buildable. All three retained ELF identities match: default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4, devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299, pool121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.

D575(A): initialize first calls PR_SET_DUMPABLE0 and setrlimit RLIMIT_CORE{0,0}, before allocating the panic hook, parsing public JSON or reading witness input. Failure emits a literal-only message and aborts before secrets. Panic=abort is retained. Linux6.8 hides pointed-to syscall arguments from the tracer after dumpability is disabled, so the finalELF limit values are checked through /proc/pid/limits. Its /proc/pid/status lacks Dumpable; the helper reports PR_GET_DUMPABLE0 using the identical diagnostics source. CoreDumping0 alone receives no non-dumpability credit.

D576(B): wallet::retain and the recovery-file writer are removed. Public wallet_output_fd must be >2, distinct from wallet_bytes_fd, valid O_WRONLY and a FIFO with device/inode identity distinct from all stdio and the input pipe. These checks precede witness reads. A duplicated owned descriptor returns the original fixed-width212-byte record through write_all at the former retention point. No framing, formatting or secret serialization to a file/stdout/stderr is introduced. The record carries every original input/change/recipient key, salt and value; the caller can derive change value using the returned record and public requested amount. DESIGN.md records all offsets and error semantics. Calling-wallet persistence is the authorized custody boundary, not a new trust item. Existing private corpora, recovery artifacts and keys remain retained and were not deleted or refunded.

## Proof result and limits

The unchanged accepted extractor regenerates actual client source before proof repair. Final-source regeneration N91106 confirms Types/Funs byte-identical and external signatures identical to those already audited; only external-template source-position comments differ. The compiled proofs and NEP audit are reused on that exact binding. parameterize.py mechanically inverts namespace/import/binder changes and proof-argument additions back to the raw computational emission. Every toStr literal receives a named certificate: its short character-list expansion proves byte size by kernel rfl, then the generic short_bound lemma uses n≤64 and U32.max_eq. No large-term decision procedure or library-object substitution is used. toStr is locally irreducible; pinned scalar maxima are already irreducible.

NEP_Driver imports all module data at private level and treats any unresolved reachable constant as a hard error. The NEP walker is byte-identical to research evidence/axaudit2-20261102/NEP_WALKER.lean. Driver changes select this client's roots/output paths and reject every axiom outside propext, Classical.choice and Quot.sound. All eight roots are complete, and raw walks equal collectAxioms. #print axioms is labelled summary-based. Final main has zero native-decision axioms; the rejected historical main is not substituted or re-credited. All5673 external objects are checked against the unchanged h4 authority before each compile, with private source/object hashes recorded.

This proves the literal bounds and removes the42 rejected native axioms from the new parametric entry. It does not supply faithful native effect instances. The former retain operation is replaced by two raw-pipe operations, increasing external operation parameters104→105; those effects, startup and OS failures remain P obligations. Formatter hypotheses still require public argument equality and shared pure renderer binding. FMT-ELAPSED-ARG, FMT-TRANSCRIPT-ARGS, E1/E2, actual RunJoin, V370/V371, L1/L2/L3, allocation/thread/pipe failure-event witness independence and native observation remain open. Resource and thread failures stay stateful world answers under rdea-2, not fixed success callbacks. No T field was added: T remains entropy_law, entropy_kernel, observation. Endpoint/deployment premise statements are unchanged: removed=[], added=[], weakened=[].

## Finite native evidence

N91110 runs the actual final production user_client and unchanged fixture executable,50 transfer/50 withdrawal, fresh per-pair proof-account labels, semaphore3, real optimized prover execution. Public statement bytes and JSON/instructions must match exactly, with only pre-registered prove_wall_seconds and baseline mask_audit excluded. Random proof bytes are not compared, and no private proof-input file is captured. The raw custody record is compared in pipe memory only and never persisted by the harness. Historical1000/100 differentials are not rerun or credited to changed code.

Every generated user file, stdout and stderr is searched for each complete raw private field and the full212-byte record. The public asset identifier is also searched and every match is retained. This is finite exact-byte-search evidence, not universal noninterference, arbitrary-encoding absence or individual-byte disjointness. The baseline fixture's legacy private outputs remain on the host and are not final-client output evidence. No secret corpus is copied into this worktree.

## Checked alias finding, failures, receipts and next work

N91105 checks a material counterexample against the superseded29f011ca binary: a distinct numeric FD>2 duplicating stdout receives all212 secret bytes. The harness checks those bytes only in memory and stores finding metadata, not secret bytes. The running old N91104 differential was stopped deliberately (authoritative exit143); its partial comparisons are retained but not counted as final. Source0e3df6e684 rejects device/inode aliases before witness input. N91109 verifies stdout,stderr and input-pipe alias controls against finalfc8808. N91107 was an uncharged reservation refusal; after fullcooldown the same-ID directory guard refused reuse and N91108 performed the corrected build. The final differential has fresh labels/output paths and an independently bound new executable; this source correction justifies its replacement run.

91007 was an uncharged resource refusal.91008 failed only on redundant local irreducibility attributes; changed source91009 passed.91010 entered the capped barrier scope but its admission scanner hit a disappearing unrelated session cgroup; Lean never started. After full180s cooldown the same-ID retry was rejected by the existing-directory guard, then91011 compiled. N91102's harness assumed strace could decode setrlimit's memory after disabling dumps; changed harness N91103 uses proc limits and passes. All failures remain in receipts. The superseded N91104 progress elapsed field had an offset-variable shadowing bug; the final N91110 driver corrects it. No result from N91104 is counted as a final gate.

Every launched job uses6G high/8G max/swap0/Tasks64; Lean-M7000, one own scope at a time. Per-attempt receipts supply exact command, exit, wall, peak RSS, swap, source revision and #print status. No unchanged full regression, package build, frozen release manifest or timing run is launched. This continuation is a focused client repair, not a formal release/deployment claim.

NEXT: wait for the existing native91110, collect metadata with collect.py, reconcile all gate results and update HANDOFF.md. Native/world binding and endpoint closure remain the next formal deliverables after these client gates.
