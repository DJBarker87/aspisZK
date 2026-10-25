# Native Terminal selector84 and prepared Claims extraction

**New checked local result:** Terminal's original 84-value native selector
equals the retained copy-helper selector, word for word, on complete arbitrary
3x29 QM31 inputs. This is a source-expression result, **not closure of Terminal,
S1, S6, initializedness or the 100-bit target**. No enclosing theorem premise
has been removed in this packet.

## Native selector result

Source freeze remains `25866ec331cc7ce27dd9956609c11d32fa8fa58a`. Its
`crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs`,
`r0::Public::terminal_qm31`, uses:

```rust
let selected = core::array::from_fn(|i| claims[i / 28][i % 28]);
```

The checked source cut has the same complete `&[[QM31;29];3]` input and
`[QM31;84]` output. It evaluates that exact expression against
`array_from_fn_copy::<_,84>(QM31::ZERO, |i| claims[i/28][i%28])`.
The generic copy helper is copied literally from the retained v3 candidate's
actual statement `src/lib.rs`, not its dummy-QM31 typecheck fixture. The
checker re-reads both source origins and verifies the exact helper body.

Each input cell has four independent symbolic u32 words in the full real
frozen core QM31/CM31/M31 types. No canonicality restriction, arithmetic/parser
stub, `kani::assume`, simplified carrier or source-byte transmutation is used.
Both outputs' four words at all 84 positions are compared, and the native
output is independently compared to `input[i/28][i%28]`. Column28 remains part
of every arbitrary input row and is correctly omitted by this 28-column
selector. The callback only reads immutable array cells: there is no digest,
query, mutable callback state, account write or external callback effect here.
This local output equality is not an adaptive-oracle transport theorem.

The smallest changed compile (`v1`) passes, then `v2` passes all143 default
Kani checks with unwinding assertions enabled at bound85. This bound includes
all84 iterations and loop exit; there is no partial-loop option. This is not a
generic theorem for arbitrary FnMut callbacks, arbitrary lengths/types, or the
other terminal array-construction sites. It does not itself connect the Rust
copy helper to every declaration in the existing Lean Terminal model.

A changed negative last-word control (`v3` compile, `v4` verification) fails
exactly at `a[83].c1.b.0 == (input[2][27].c1.b.0 ^ 1)`: 1 of95 checks fails.
It confirms the final output comparison is active and is excluded from the
accepted positive result. There is no repeated unchanged positive proof run.

| Attempt | Outcome | Exit | Wall s | time RSS bytes | Sampled aggregate RSS bytes | Swaps |
|---|---|---:|---:|---:|---:|---:|
| selector v1 | compile only | 0 | 0.691428 | 121978880 | 17514496 | 0 |
| selector v2 | 0/143 failed | 0 | 3.621465 | 416169984 | 415727616 | 0 |
| negative v3 | compile only | 0 | 0.450627 | 119685120 | 22609920 | 0 |
| negative v4 | expected last-word failure | 1 | 2.728372 | 254083072 | 318111744 | 0 |

Positive solver time3.2258391s. Atomic shared local lock, one Cargo job, warm
cache and the existing2GiB/64-process/180s watchdog were used. No stop fired,
unknown lock was removed, NUC/SSH operation or source adoption occurred.
Very short jobs can finish between RSS samples; the sampled aggregate is not
a complete historical peak census. Default Kani checks **do not establish
initializedness**, and these Mac/aarch64 results do not establish Linux/SBF
compiler/Std/artifact identity or a no-swap OS policy.

Exact per-attempt source/tool/sysroot library/manifest/lock/command/environment
pre/post pins and raw outputs are retained under
`evidence/s126-current-caller-20261021/s1-terminal-selector-v1` through `v4`,
with the source-only manifest in `s1-terminal-selector-20261025`.
`#print axioms`: N/A, no Lean target or custom axiom was added. Maintained
proof/tools/report whitespace is checked separately from pinned raw logs.

## Existing native prepared_claim connection reused

Before launching another whole prepared-claim experiment, the prior source
packets and failures were inspected. The old timeout is superseded by the
existing `S1-NATIVE-WORD-CONTROL-20261024.md` packet: seven bounded normal-return
cases already establish original/borrowed-reference Result and complete
numeric child-call equality, with an exact finite first-error partition and
baseline reference extraction. Its source-only checker was run and passed;
no compiler, solver, extraction, old failure or unchanged Lean proof replay
was run for that evidence. Concrete numeric leaf interpretation and abort/
effect/source-oracle/caller installation remain open; these are the next
joins, not a reason to repeat the already checked normal-return comparison.

The existing native finish selectors cover sizes16 and10; they are also
reused, not replayed. This new84 result fills a distinct pure source-expression
check. It does not promote either packet to a whole Terminal proof or silently
adopt the copy helper in the frozen statement source.

## Candidate Claims extraction: PREPARED, NOT RUN

The isolated safe-storage candidate in commit891a213f79 still has no adoption
decision. A reproducible source-only kit now contains the exact typechecked
candidate body, full frozen wire/sampler/core inputs, unchanged two-package
lock, explicit workspace metadata, and focused Charon/Aeneas commands.
The v2 plan includes actual Prefix getters and `heap::filled`, retaining the
decoder as the existing named child boundary rather than re-proving the
other owner's parser. No live dependency/cache or production file was changed.

Prepared read-only source release:
`/private/tmp/s126-claims-safe-extract-source-release-20261025-v1`.
Its98 source/plan files have exact pins; the plan has97 supplied source files.
Plan SHA256:
`a5cce7a846276a3ed9113d97052b1d34aca65707b83934651e2e3fe5b9ad0c84`.
Source/plan hashes and modes were checked before and after publication; this
is a prepared SOURCE release, not permission to inspect any live cache or run
a compiler. The only supplied run marker raises SystemExit unconditionally.

The proposed separate extraction/translation scopes are High1536MiB,
Max2GiB, SwapMax0, Tasks64, using the earlier pinned tool locations and owned
warm target. **Neither phase has run.** Fresh complete reviewed admission,
current tool/runtime/import pins and no-writer cache checks are prerequisites;
the lead's metadata-only GO does not authorize this extraction. Old receipt
tool hashes are not relabelled as prospective execution evidence.

The v1 preparation is retained too. V2 adds explicit source getter includes
and an exact preparer-source snapshot; it is not a compiler retry. No exit,
wall/RSS, axioms or generated model result is invented for unexecuted commands.

Remaining adoption gates from the candidate report still apply: extraction
and ordinary kernel validation, all-outcome native equivalence or reviewed
replacement refinement including allocator/error/drop/effects, actual caller
installation, CU/stack/two-transaction checks and source/artifact re-pins.
The frozen body's allocation/union initializedness proof remains open.

Integrity checks, without replay:

```
python3 tools/s1-terminal-selector-20261025/check.py
python3 tools/s1-claims-safe-extract-20261025/check.py --released
python3 tools/s1-claim-word-checks-20261024/check.py
```

The native Claims trace packet's historical `expected_time` text still says
one-row/initialization in part of its inherited caption. Its actual command,
kind, source, target and report specify the complete function with DEFAULT
checks. Those raw historical bytes are not rewritten and confer no
initialization-check credit.

The exact remaining enclosing premises are unchanged: explicit base Ops,
FinishModel Claims/Terminal, native numeric/Std/allocator/abort/effect and
arbitrary-prefix/source bindings, plus the shared original/current/kernel/
event/oracle/release joins. S2 remains with its transferred owner; the shared
S6 join remains lead-owned. Both source-freeze choices and the target security
contract are preserved; whole S1/S6 and <=2^-100 per attempt remain unestablished.
