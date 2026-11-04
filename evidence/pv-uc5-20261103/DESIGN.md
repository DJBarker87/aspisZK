# D577 client custody and proof repair

Continuation base `0e8a457c55`, branch `codex/pv-uc-20261029`. D575(A) and D576(B) authorize these three user-client source edits only. No crate, program, lockfile, manifest, fixture target or protocol encoding changes. No RPC, deployment wallet access, timing experiment, key cleanup, push or merge.

The inherited `prompt-pv-uc4.txt`, `prompt-pv-uc3.txt`, pv-common.txt, r1p-common.txt, local-lean.txt and the root AGENTS.md were read. Their older `prompt-pv-uc.txt` is absent; `prompt-pv-uc-s1.txt` also references that absent file. The preserved reports, source and research LOG D525 were consulted. D525 freezes statement/proof wire bytes and TX1/TX2 layouts, excludes the live deployment, and retains the fixture SDK pin. These conditions remain unchanged.

## Startup

The first call in main remains diagnostics::initialize. Its first application operation on Linux is PR_SET_DUMPABLE(0), followed by setrlimit(RLIMIT_CORE,{0,0}), before panic-hook allocation, environment setup, JSON parsing, threads or witness input. Either syscall failure emits only `client startup failed\n` and aborts before any wallet read. The fixed Linux ABI is the pinned x86_64 Linux binary. The successful path retains panic=abort and literal-only diagnostic hooks.

Linux 6.8 omits the historical `Dumpable` field from /proc/self/status. A captured `CoreDumping: 0` is not proof of non-dumpability. The runtime gate records that status and core limits for the final ELF, its hardening syscall trace, and PR_GET_DUMPABLE=0 from a helper using the identical diagnostics source. It also forces both an early final-client panic and a post-wallet-read final-client panic. This reports the actual kernel interface instead of inventing an absent status field.

## Output custody

Public JSON adds wallet_output_fd: an inherited descriptor >2, unequal to wallet_bytes_fd. The final0e3df6e684 guard also rejects identical device/inode identities with stdin,stdout,stderr or the input channel, since distinct descriptor numbers can alias one pipe. N91105 demonstrates the numeric-only check leaked the212-byte record onto stdout in the superseded binary; N91109 tests all three alias controls on the repaired final binary. F_GETFL must succeed and report O_WRONLY. A duplicated owned descriptor must identify a FIFO through fstat metadata. These checks occur before reading witness bytes. The application never opens a recovery file and never formats a witness.

On the successful plan path at the former recovery-write point, write_all returns exactly the original 212-byte N7 record to this raw pipe. It contains every original input/change/recipient key and salt and their values; the caller already knows the public output amount and can compute the change value. The record layout and little-endian encodings are unchanged: input key 0..31, input salt 32..63, input value 64..71, asset 72..75, change key 76..107, change salt 108..139, recipient owner 140..171, recipient salt 172..203, recipient value 204..211. No framing, formatting, JSON, path, newline or file persistence is added. The calling wallet owns storage. Existing historical recovery files, keys and private corpora remain retained; removing the writer does not authorize deleting them.

A closed reader, descriptor exhaustion, metadata/write failure and SIGPIPE remain runtime failure paths. Their occurrence/timing and caller-world independence remain obligations under rdea-2; the pipe is not guaranteed successful and adds no T item. Descriptor checks expose only public FD metadata.

## Lean proof repair

N91100 regenerates the actual changed client using the already accepted pinned Charon and functionally identical Aeneas rebuild. The parametric envelope preserves every emitted computational body, replacing only namespace/import/binder lines and the implicit toStr proof arguments. Its 68 literal occurrences use 42 distinct named certificates. Each literal's short ASCII character list has its byte size proved by kernel rfl; short_bound combines that equality with n≤64 and the named U32.max_eq theorem using linear arithmetic. No maximum numeral or recurrence is normalized by decide/native_decide. The pinned U32/U64/Usize maxima are already irreducible; toStr is locally irreducible in Funs. The first Funs attempt 91008 rejected the redundant local max attributes before credit; the corrected 91009 removes those attributes without changing any function body.

The carrier/operation parameters remain explicit obligations, including diagnostics initialization, output channel and raw record return. Standard-only entry compilation/audit does not instantiate those external effects, establish honest-run non-emptiness or remove a privacy endpoint premise. NEP_Driver uses importAll=true and private module data, with hard failure on unresolved reachable constants; its walker source is retained verbatim and its driver adaptation is explicit.

## Gates and evidence classes

The 100-pair differential executes the final production user_client and unchanged fixture executable, 50 transfer and 50 withdrawal. It compares public statement bytes, public JSON and instruction bytes with only the previously registered timing and removed mask_audit exclusions. It captures no proof-input file. The output pipe is checked in memory against the exact input record and never persisted by the harness. Random proof bytes are not compared.

Every user-generated file, stdout and stderr is searched for each full-width raw input field and the complete record. Both complete key/salt/record results and all scalar-word matches are recorded; scalar collisions are not suppressed to manufacture a passing literal gate. This is finite exact-byte-search evidence, not universal noninterference or a side-channel proof. The fixture's legacy witness/mask outputs remain baseline-only private artifacts, not final-client output evidence.

Retained release ELF bytes are rehashed against all three frozen pins; prior fresh SBF builds are reused because only tools/r1-cost-probe/src/bin/user_client source changes. No timing measurement is authorized in this continuation.

The first completed pairs exposed a harness-only progress timer shadowing bug: the per-field `start` offset replaced the global timer only inside pair. Final summary and resource receipt timers are independent. The committed driver now uses field_offset for future runs, without uploading or modifying the active N91104 source; its receipt/staged hashes preserve the executed script. No prover/output/comparison logic changes, and no differential is resubmitted.
