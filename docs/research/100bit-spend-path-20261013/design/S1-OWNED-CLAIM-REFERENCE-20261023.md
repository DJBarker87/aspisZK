# S1 owned nested-claim reference — source candidate, not closure

Frozen S1 and S6 remain OPEN. The per-attempt target is still <=2^-100,
without grinding/work normalization. S2 remains transferred to its new owner;
no S2 or other owner's proof/source track is modified here.

## Established

An isolated owned reference of the complete nested claim now extracts with
Aeneas. Its public input is the FULL `Verified<H>` owner, an exact 928-byte y1
array, the complete 29-element gamma array, inactive and kappa. It returns the
same semantic owner on both Rust result paths. It does not clone or allocate
the boxed claims. Scalar arrays are copied into the loop helper; a scalar
helper receives owned arrays; a push helper returns its complete Dot state;
the final sum helper borrows the two seven-element arrays. Both original
nested ranges and their early-error exits are retained. This is a proof-only
reference; no production source or ELF is adopted or changed.

`S1ClaimOwnedNestedModelV1.lean` materializes the generated bodies on the
existing complete nominal carriers and explicit `ClaimDotOps D` ports. It
reuses the retained zero, release trace, add and mul definitions. The
`Result::is_err` implementation is the ordinary constructor case split; no
custom axiom is introduced. Private array extents are generalized to N in
Lean to avoid a concrete928 elaboration issue; the public owner wrapper
remains exactly 928 and specializes those unchanged bodies to 928. The raw
fixed 928 output, templates and exact materialization are retained for audit;
no raw axiom/template is imported into the checked module.

`S1ClaimOwnedNestedTransferV1.lean` proves:

- `scalar_eq`: the copied rows and same y1 slice give exactly the retained
  scalar read, for every point/column and arbitrary operations.
- `sum_eq`: the emitted sum is definitionally the retained source sum.
- `owner_frame`: either Rust result from the full wrapper returns exactly
  its input semantic owner and the same loop result.
- `owned_step_some`: the emitted active inner iteration equals its explicit
  read/weight/push/error/state transition, with no child-success assumption.

The native source step certificate compares the original statement containing
`dot.push(g[l],scalar).map_err(|_|Error::Parse)?;` with the copied-input step
using the SAME helpers as the extracted owned reference. It quantifies over
all six points/all 29 columns, arbitrary complete native Dot pre/poststates,
arbitrary actual semantic numeric fields, all gamma/y1 bytes, and either
push result. It checks complete push inputs, poststate, error mapping, field
count and the exact 32-byte field frame/index. The actual `Verified` and Dot
types are used; no reduced carrier or output-only comparison is used.

This is coupling under explicitly shared arbitrary push and field ports.
The field port observes the same admitted 928-byte length and actual 32-byte
frame; it is not an independently proved implementation of `weights::field`.
The concrete digest context is an unused Hash marker whose digest panics if
called. Actual leaf installation, generic/P6 carrier transport, allocation/
runtime admission and enclosing native execution are NOT discharged by this
certificate. Do not turn the port coupling into a claimed source proof by
assuming the desired whole-call equality.

## Validation and pins

Source-only `focused-extractor-proof-packet-v1` packets:

- `evidence/s126-current-caller-20261021/s1-claim-uf/`: exact inputs, tool hashes,
  commands, failed alternatives and successful owned extraction v7.
- `evidence/s126-current-caller-20261021/s1-claim-owned-reference/`: raw generated
  source, materialization and successful native source-step packet.
- Focused Lean receipts `s1-claim-owned-model-v3` and
  `s1-claim-owned-transfer-v13` in that same evidence root.

| Target | Exit | Wall seconds | Peak RSS | Swap |
|---|---:|---:|---:|---:|
| owned reference v7 Charon | 0 | 0.326 | 209884 KiB | 0 |
| owned reference v7 Aeneas | 0 | 0.740 | 101024 KiB | 0 |
| native original/owned step | 0 | 114.069 | 2382904 KiB | 0 |
| Lean model v3 | 0 | 19.520217334 | 3234627584 bytes | 0 |
| Lean transfer v13 | 0 | 17.123882958 | 3279519744 bytes | 0 |

Native Kani: 828/828 checks and 3/3 covers. Explicit opt3, MIR opt0 and overflow
checks; seven active local path dependency inventories unchanged before/after.
NUC jobs have fresh admission and MemoryHigh=6G/MemoryMax=8G/MemorySwapMax=0;
metadata uses 1G/2G/Swap0. Local Lean uses the atomic lock, -j1 and -M4400.
The current model/transfer axiom reports are standard-only. Source/tool/
import pins and full logs are in receipts; no binary is distributed. These
are focused cached checks, not a coherent release rebuild.

Freeze remains 25866ec331cc7ce27dd9956609c11d32fa8fa58a, with the standing S4
adoption 29cbab4317; no different working-tip source is silently re-pinned.
Read-only S2 authority hashes are in `s1-claim-uf-authority.json`: S2-E's
reference certificate is merged, but F native equality/G child installation
were still open at inspection. S6 does not assume that reference acceptance
already supplies the native execution cuts.

## Excluded attempts and remaining obligations

Whole-point Kani checks still time out at 180 seconds, including the UF,
no-propagation, replay and accepted-only replay variants. They have NO
semantic credit. UF positive/negative controls validate congruence and input
sensitivity only. Replay v1 also exposed a 168-byte memcmp with insufficient
unwind 128; v2 uses equivalent scalar comparisons, retains every check, and
still times out. No timeout was rerun unchanged with a larger memory cap.
Owned extraction v1–v6 failures are retained; v7 succeeds after keeping the
owner outside the loops and using a borrowed sum helper. Failed Lean drafts
have compiler-error/sorryAx diagnostics and are not accepted proof evidence.

`S1ClaimOwnedOuterCompleteV1.owned_claim_eq` now establishes the enclosing
reference claim equality, rather than assuming a child-loop join:

```text
forall D H N ops digest sem y1:Array U8 N inactive kappa g:Array E29,
  owned_claim_loops ops sem.claims sem.extra sem.before_z1 y1 inactive g kappa
  = prepared_claim ops digest sem (Array.to_slice y1) inactive g kappa
```

`complete_owner_eq` lifts this to the full public owner wrapper, returning
exactly the input semantic owner on either Rust result. Both results are
complete Result equalities, including child fail/div and Rust Err. They retain
the same explicit primitive ports. No desired dot value, child success,
canonicality, pending-return shape or whole-call equality is a premise. The
inner/outer cursor proofs derive finite budgets30/7; arbitrary child divergence
is preserved, so this is TOTAL control/equivalence, not actual-child totality.
The contextual inner theorem discharges the impossible early-Ok pending case
inside the outer proof; it is not assumed independently.

New focused targets: `s1-claim-owned-loops-v4`17.097528333s/3237003264B,
`inner-complete-v1`18.624373458s/3221274624B,
`inner-cps-v1`21.380617792s/3224698880B,
`outer-step-v2`20.649163292s/3238051840B and
`outer-complete-v5`17.682020208s/3244195840B. All exit0, swap0 and standard-only
axioms. Complete target names/commands are in receipts and the focused import
pin file. No unchanged whole replay was run.

A new native dependency audit found six differing Rust files in the initially
cached statement crate. The original native step result remains qualified to
its exact inputs; before/after stability alone did not establish the full
adopted dependency freeze. The corrected `native-source-step-strict` packet
copies the adopted statement crate and its10 external Rust imports byte for
byte, and rechecks the SAME native step against that graph. It passes828/828
checks and3/3 covers:82.532s,2383608KiB,swap0. All223 compared active dependency
source files match, apart from the explicitly recorded cfg(kani) input
constructor. Cargo workspace/path metadata and a proof-only prerelease package
version are recorded; the latter avoids an inactive host-prover lockfile
collision. A locked, capped metadata query records exact active features and
confirms the proof's lockfile hash. Metadata/package/include preflight failures
are excluded; they yielded no source-equivalence evidence.

`borrowed-abi-extraction/` additionally retains candidate v9: an original-ABI
wrapper borrowing the FULL `Verified`, y1 slice and gamma array, with private
owned scalar arrays/Dot state. It extracts successfully (Charon0.339s,
Aeneas0.778s, swap0). This avoids a fixed928 public restriction and needs no Box
clone or byte-buffer allocation. It is extraction feasibility ONLY; its new
public-wrapper/body transport and native/caller instance are the next task.
The accepted kernel equality above applies to the separately pinned v7 model,
not silently to this new candidate.

Original native whole-loop/caller correspondence, primitive installation,
shared original Prepared.new/tx1 source connection and whole-caller arithmetic/
actual-child totality remain open. The normal-return native leaf-port harness
alone does not establish actual leaf totality or panic/abort transport. The
existing parsing, canonicality, shared gamma powers and joint challenge-trace
proofs remain the intended consumers/providers. No enclosing actual frozen
Prepared.new/first premise is reported removed by the reference equality.

S6 still needs the actual S2 stage1 execution binding and its original-byte
statement transport, then a join to `first`/`first_decoded` reuse preserving
validation, errors, observer None, copy/cleanup and account effects. No whole
S1/S6 obligation or global 100-bit soundness conclusion is claimed here.
No frozen-source decision is adopted by this packet. Adopting any refactor
would separately require source equivalence, affected proof/import re-pins,
CU/integration gates and exact source/artifact adoption.


## Borrowed ABI follow-up

The new `S1ClaimBorrowedAbiTransportV1.borrowed_claim_eq_source` proves full
Result equality between the extracted borrowed reference and the retained claim
model for arbitrary byte slices, arbitrary shared `ClaimDotOps`, and the same
semantic input, gamma powers, inactive claim and kappa. There is no fixed928,
child-success, canonicality or accepted-run premise. The internal array witness
is a logical view of the same list, not a runtime allocation. This removes the
owned-y1 interface restriction from the reference theorem; it does not establish
original native whole-function correspondence.

The three new focused targets passed with Lean 4.32.0, `-j1 -M4400`, zero swap:

| Target | Wall seconds | Peak RSS bytes | Axioms reports |
| --- | ---: | ---: | ---: |
| S1ClaimSliceCarrierV1 | 4.968222333 | 3171762176 | 2 |
| S1ClaimBorrowedAbiNativeV1 | 12.087661708 | 3184934912 | 1 |
| S1ClaimBorrowedAbiTransportV1 | 19.942321167 | 3213950976 | 9 |

All reports use only propext, Classical.choice and Quot.sound (the carrier uses
only propext and Quot.sound). Exact source/tool/command/import hashes are in
`s1-claim-borrowed-abi-import-pins.json` and the accepted target receipts. No
unchanged full replay ran. The failed initial transport edit remains evidence.

The original native one-step check against this borrowed reference passed all
824 assertions and 3 covers: `s1-original-borrowed-step-v1`, exit 0,
66.851 seconds, 1575724 KiB RSS, zero swap, cgroup 6/8 GiB and SwapMax=0.
Its complete source, admission, dependency checks, commands and logs are under
`evidence/s126-current-caller-20261021/s1-claim-owned-reference/native-borrowed-step`.
It uses coupled arbitrary normal-return child operations. This check does not
prove actual child totality, panic/abort behavior, the original complete loops,
or the enclosing Prepared::new / tx1 caller.

S1 and S6 remain OPEN. Remaining S1 obligations include the original complete
native execution/caller connection, actual child range/totality and mutable
serialization binding. S6 still requires the actual stage-1 caller connection
and full ASF8 public-statement encoder/decoder contract identified by session A;
existing decoded-public reuse alone does not discharge them. No production
source was changed or adopted. Any candidate adoption requires source
equivalence and explicit source/artifact re-pinning.
