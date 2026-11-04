# D609 — original caller execution to route B

Research only, 2026-11-04. No Lean, native, Kani, extractor or build run.
No theorem or native edge is discharged by this document. No endpoint premise,
domain, observer, simulator or trust field changes. Privacy target not established.

## Finding and recommendation

**Use (c), the existing ruling-(y)/(y') per-caller hybrid certificate, for the
missing ORIGINAL caller association. Reuse (b) for the bodies actually covered
by extraction. Do not commission a general LLBC interpreter.** In particular,
the current fixed-handler no-regression bridge does **not** already prove the
requested original frame/control/loan theorem. Neither an additional blanket
Rust=extraction premise nor a supplied desired route-B configuration repairs it.

There are two distinct questions:

1. What is the admitted semantics of a specifically associated extracted body?
   D188 already answers this, subject to its narrowing and pins.
2. Does this reconstructed, effectful Code program implement the ORIGINAL
   caller with the same receivers, places, effects and continuations?
   The present value-erasure theorem does not answer this. The native caller
   certificate and source-to-Code composition must answer it.

Logical source frames/borrows are the subject here. Physical stack slots,
native handle layout, padding, zeroization and compiled frame residence remain
V370/L3 work under D581/D588, not consequences of functional extraction.

## Sources and frozen inspection points

All other branches were read with `git show`, never by accessing their worktrees.
The branch tips inspected were:

| Branch | Revision |
|---|---|
| this research worktree, before this report | `cc6e07b9cd5ca056c4a0c9e422a88b019eaa2467` |
| `codex/pv-b3p6-20261028` | `a9a485bd7861ac3ee9ece63983d0d2655159d0da` |
| `codex/pv-evhB-20261103` | `54d51de0ad8f6f42c0aad2c32f762c99dd05e972` |
| `codex/pv-stx-20261104` | `816756d85f11e3af6af1444303eb9530edd701c4` |

Authoritative policy paths at the research revision:

- `docs/research/v8-r0-zk-20261009/LOG.md`, D188, D190, D301–D302,
  D605–D608. This checkout's LOG ends at D608; D609 is this research question,
  not an already committed ruling found in that LOG.
- `docs/research/100bit-spend-path-20261013/design/SECURITY-CONTRACT-20261021.md`,
  first 2026-10-27 amendment §2, second amendment §3, third amendment §§1–3,
  fifth amendment §1 and standing delegation.
- `design/PV-OWNER-PACKET-20261027.md`, opening D188/fifth-amendment paragraphs;
  `design/PRIVACY-LEDGER-20261026.md`, “Standing rulings” D188 paragraph
  (line 522) and owner decisions.
- `docs/research/100bit-spend-path-20261013/design/C3-BIN-20261021.md`,
  ruling (y), 2026-10-29, and (y'), 2026-11-01. Stream A read-only throughout.

Worker evidence at the respective pinned tips:

- b3p6 `evidence/pv-b3p6-20261028/resume18/BLOCKER-557.md`, item 4;
  `HANDOFF.md`; `lean/PV_B3P_{SelectionCode603227,SelectionLoan603227,
  SelectionReach603227,SelectionScalars606227,SelectionBinding13227,
  TopDown13227,Install227}.lean` beneath the same evidence root.
- evhB `evidence/pv-evhB-20261103/OWNER-D605.md`.
- stx `evidence/pv-stx-20261104/VERTICAL-SLICE.md`, root `HANDOFF.md`,
  `lean/PV_STX_{Code,Machine,CleanupBridge,SourceEntry}.lean`.

The worker markdown can lag its branch source: stx's current SourceEntry
defines a parameterized `source_entry_world`, although its older handoff says
none is defined. The source expressly leaves concrete installation/native
binding open. Definition and projection equations are not that binding.

## Exact existing authority: what D188 says

LOG D188: “the project's source semantics are the Charon/Aeneas extractions”.
It places Rust/extraction correspondence in `AeneasExtraction`, and source to
deployed binary at S10 plus P7. It explicitly retains non-extracted wrappers
and traced outer composition as proof work; child-internal events are not
silently supplied by the outer trace.

The first owner amendment, §2, states:

> D188 is read at trace fidelity. We trust the pinned Charon/Aeneas
> translation of each specifically associated shipped Rust body to preserve
> both the accepted Result and the chronological attempted digest-call
> sequence of its monadic extracted execution, including duplicates and every
> issued call before rejection; rejected prefixes must both reject, with
> differing non-Ok error kinds allowed (the recorded Err(Parse) versus
> extracted fail-panic discrepancy).

It continues: SAME body, inputs, digest replies and source/producer pins;
not an arbitrary recorder or caller. Non-extracted wrappers and unsafe
construction still need P6; L166 must be proved from the extracted trace.
This is **not** blanket fidelity of every syscall, allocation, physical frame,
event codec, failure timing or invented world handler.

The second amendment, §3, states:

> D188 (the pinned Charon/Aeneas translation is the semantics of each
> translated shipped body, at trace fidelity) is narrowed to bodies that pass
> both a static scan for the dropped-restoration pattern and a native
> differential on inputs where their writes matter.

Failed bodies become opaque leaves needing native P6 bridges to the cohort
model. Mutable-iterator/element-accessor writes have no credit until checked.
LOG D301 records owner approval; D302 restores the four named overlapping
functions under their checks, not arbitrary other bodies. The owner packet
explicitly says fixtures do not establish universal chronological-trace fidelity.
The third amendment permits direct native bridges, composing along proved
caller domains. The fifth records cross-tool transport as existing P6/D188
trust, **reclassification**, never proof removal. No extra RunJoin T field.

## Alternatives: proof, trust, decision and cost

| Route | What it would establish | Trust / owner decision | Cost and present limit |
|---|---|---|---|
| (a) New Lean LLBC interpreter | Executing represented LLBC frames, moves, branches, borrows, returns and restoration; a proved simulation could relate those executions to Code and derive cuts from entry. | Its internal Lean theorems need only kernel logic. An interpreter alone proves NOTHING about rustc execution. An unproved assertion that it faithfully interprets rustc/Charon is a new semantic trust surface, requiring owner approval under the privacy rules; it cannot enter the capped T. It avoids new trust only if its association is proved through an already accepted semantic boundary, or independently certified by existing P6. | Highest cost: semantics, instantiated types, place/projection/move rules, borrow/provenance, globals, initialization/drop, failure/resource behavior, entry binding and whole-cone simulation. Existing JSON plus parametric read/write laws supplies syntax/administration only. Implementing just enough for three sites still needs original entry and loans. No justified numeric runtime estimate exists. |
| (b) Existing narrowed extraction plus route-B bridge | D188 supplies source association for eligible, actually extracted bodies. Their monadic syntax fixes value dependencies, branches, argument values, and emitted backward continuations. A proved operational lift can derive logical continuations from that syntax. | Existing pinned D188, verified local transformations, applicable native leaf bridges, plus retained compiler/artifact boundary. No owner decision to use these within their stated scope. Treating a value equation as arbitrary-world event/loan fidelity, or broadening digest trace fidelity to all native events, is unsupported; trusting that extension would need an explicit decision. | Lowest incremental cost where the original body is actually extracted and lift is syntax-preserving: local administrative simulation and primitive installation. Does NOT close the present op227 gap: it is external in ProverRwFull; reconstructed selection uses a reference extraction and a different administrative order. |
| (c) Ruling (y)/(y') native per-caller certificate + Lean composition | Frozen caller under exact features, arbitrary full child replies and declared modifications: exact arguments/places, caller Result, final state, ordered effects and child domains as G(inputs, local log). Closed child contracts substitute at those same places; Lean proves G with substituted children equals the Code/cohort model. Borrowed returns preserve the contract-designated actual place. | Existing P6/D188 transport, amendment five option A, approved tool controls, existing child/runtime contracts, compiler cohort and source/artifact pins. No new owner decision for the stated pattern: (y) is an existing method decision, (y') a clarification. Label hybrid/reclassification. Additional trust for unchecked pending/fault semantics or OS traces is NOT authorized by (y). | Medium, repeated per caller but reusable by shape: one native iteration from arbitrary state for loops; one exact caller log/schema, child/place contracts, controls and Lean composition. Kani handles control/index/loan plumbing; field arithmetic remains Lean with cited identical pure abstractions. Whole-cone coverage and original entry still cost real proof work. |

For (c), the ordinary returning `Result` certificate must not be advertised as
a proof of blocking, divergence or fault prefixes. Extend the **proved** Code
substitution/simulation to all primitive Reply cases using their separate
source contracts; retain native pending/request-start/timing obligations where
those contracts are unavailable. Ruling (y) alone does not discharge them.

## Why (b) does not already close these three workers

At the b3p6 pin, `ProverRwFullExternalFuns.lean` in
`docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/` declares
`op227` and aliases `Public.terminal_qm31` to it (lines 742–747, 1040).
There is no original op227 body there from which its internal frames follow.
The separately generated `PV_B3P_P227_14.lean` calls
`PV_B3P_227.reference_terminal.select227`; its source is `reference_terminal.rs`.
`source_selection_binding13` binds to that reference, not the deployed wrapper.
`PV_B3P_Link_terminal_qm31` remains an explicit wrapper equation. Choosing
`Install227.selected`/a dictionary satisfying it is not proving it at original ops.

`SelectionCode603227.claim` evaluates quotient, row request, remainder, column
request. BLOCKER-557 records the ORIGINAL LLBC remainder before row29177.
`SelectionReach603227.afterRow` actually recomputes remainder after row.
`SelectionScalars606227.indices` proves literal-28 division/remainder total,
so moving that pure scalar computation may be proved silent. But fixed-denote
equality does not itself prove the movement, state framing or stack relation.
A final value can agree after calls were reordered or effects erased.

`SelectionLoan603227.store_erases` composes `Array.index_mut_usize` and its
back function to Array.update under **fixed** interpretation. Its
`borrowed_continuation` retains whichever `(old,back)` the handler returned.
Neither proves that native loan35 is that borrow of the same original buffer.
OWNER supplies storage/provenance relations, not original caller selection.

Similarly, `PV_STX_Code.denote` contains no world. `start_denote` and
`CleanupBridge.generate_erases` preserve value Results; they do not construct
the actual activation, live regions or native drop effects. LOG D190 expressly
requires a checked transformation or sufficient observational transport for
the stateful lift. evhB's handles receiver must be borrowed **before** spawn;
the task returned at that SAME world must move into that receiver's push.
That association is exactly a caller-log/place obligation, not allocator adequacy.

## First concrete deliverable under (c): the original selection caller

Proposed certificate/theorem package name:
`PV_B3P_OriginalSelection29177_29182_29187`.
This is a mathematical specification for new work, **not existing Lean API or
a type-checked declaration**. No invented interpreter/Reached hypothesis is
being asserted. State the native and kernel portions separately, as (y) does.

**Native caller certificate (first gate).** For every invocation in the
UNCHANGED admitted original op227 domain, begin at original function entry
with its actual arguments, admitted outer continuation and SAME OWNER world.
Execute the original prefix including statement74 ArrayRepeat. For every
reached loop iteration, certify the following G/log law with symbolic contents,
not just i=0 or a supplied initialized buffer:

```text
OriginalCallerPrefix(inputs, primitive answers)
  = G29177_29182_29187(inputs, local ordered child log)
```

Equality means caller Result, state and ordered declared effects, with exact
borrowed-place identities. The native certificate must DERIVE:

- Initially selected = repeat(QM31.ZERO,84), i=0; later selected is precisely
  the SAME buffer after previous iterations' writes. local6/local7 derive the
  true i<84 branch; otherwise the loop exits without these three calls.
- q=i/28 and r=i%28 are computed before the original row call
  (86/89 and 95/98); q<3 and r<29 follow, not assumed.
- 29174/local30 is the actual claims receiver; 29177 takes (claims,q),
  returning destination31. 29179/local32 is that returned row/place;
  29182 takes (SAME row,r) and returns reference33/value v.
- 29184/local34 and local14 identify the same selected buffer and i;
  29187 borrows that element and returns loan35. The assignment writes v
  through that SAME loan; restoration updates selected[i] and frames other
  elements/owners. The continuation retains the original outer caller.

Use (y') for references, never arbitrary fabricated references. The row/column
accessors here are array indexing, not automatically the pure field-getter
exception: supply the actual designated-place child contracts and bounds.
An arbitrary child reply cannot replace an alias/provenance obligation.
The native harness records caller-local logs only, no writable statics, with
matched wrong-row, wrong-column and wrong-loan/place controls. Apply KMX where
needed; deployed feature/profile and std parity/compiler-cohort qualifications
are mandatory. No field multiplication chain is sent to Kani.

**Lean composition theorem (first kernel target).** Define the literal
source-order Code lift for this prefix, with quotient AND remainder before
the row request, and original initialization. Prove from that entry syntax:

```text
For every admitted input, outer continuation, initial OWNER state, and every
primitive answer history satisfying the separately certified local contracts:

  the source-order lift and the existing SelectionLoan603227.select machine
  have corresponding finite prefixes (allowing silent administrative steps),
  with the same reached row/column/borrow/restore requests, complete Replies,
  post-worlds and ordered events; all final Results/faults agree, and every
  pending request retains its corresponding continuation.

At row29177 on a true iteration the existing-machine configuration is:
  code = call (read (row claims q))
  kont = seq (SelectionReach603227.afterRow i)
           (seq (SelectionReach603227.afterClaim selected i) outer).

At column29182 it consumes the SAME row returned by row29177 and r.
At borrow29187 its reply (old,back) is retained, and the next store request is
  call (SelectionLoan603227.Request.restore back v),
under the same store caller, at the borrow's post-world and event prefix.
On successful native restoration returning typed selected1,
  Result.ok selected1 = Array.update selected i v,
with the OWNER relation to that very source buffer preserved.
```

The local contracts above are child/primitive proof obligations, not new
endpoint premises. Prove the administrative relation, including moving the
total silent remainder, using `indices`/`bounded_indices`, rather than treating
Code configurations as equal or fuel counts as identical. Pending row resumes
the same request; no success premise may erase failure/pending branches.
The prefix theorem relates matching cuts, not arbitrary equal-fuel prefixes.
The native returning certificate plus this theorem is a hybrid association;
it is not a single kernel theorem interpreting Rust. Outstanding native
nonreturning/effect contracts remain explicitly outstanding.

This is the smallest useful first result because it tests initialization,
control, two dependent borrowed reads and mutation/restoration together. A
statement starting with i<84, selected, Reached or the desired Config cannot
serve as the original-entry certificate. The existing `body_row_cut` is a
useful internal lemma after those facts have been derived.

Then extend caller certificates across the 967 edges/540 builtins and actual
helper environments; compose semantic141/terminal-parts173 and prove the
UNCHANGED original-ops wrapper equation in BLOCKER-557 item5. For evhB apply
the same pattern to receiver-borrow → spawn → returned-task move → push on
the actual handles owner, including pending realloc phases. For stx apply it
to the actual entry activation/capture, then instantiate Installation and
derive projections from that one source run. None follows merely by sharing
the certificate shape or by importing OWNER.

## Validation and obligation accounting

Read-only source/policy inspection and documentation diff checks only.
No generator `--check`, native differential, Lean elaboration, axioms audit,
Kani certificate or full regression was performed; no execution receipts are
claimed. The proposed statements require implementation and validation in
the workers' separately authorized jobs. Premises removed 0; retained: original
caller/entry association, primitive/OWNER installation, actual-ops wrapper
equation, native effects/resource independence, V370/L3 and release binding.
Added trust items 0. Stream A files and all keys/accounts untouched.
