# What remains before the soundness claim

This page sets out what still stands between the assembled theorem and the
claim I intend to make for the current version: that its spend path, as it
actually runs, has 100-bit classical soundness per attempt, with no
proof-of-work or grinding credit. That target is not yet established. The facts
below come from the status document as it stands on the `research` branch at
commit `cfa09f5e2c4` (10 November 2026), the same commit the copy in this
folder, [`SOUNDNESS-STATUS.md`](SOUNDNESS-STATUS.md), was taken from;
each paragraph ends with the section of that document it rests on.

Several of the earlier items are done. The two theorems compile with only
Lean's three standard axioms; the whole closure, 14,101 modules, has been
rebuilt cold from committed sources and both theorems re-checked on the rebuilt
objects alone; both release ELFs have been rebuilt byte for byte from the frozen
source; and an axiom audit of the rebuilt closure finds 105 nonstandard axiom
declarations in it, none of them reachable from either theorem (section 6,
items 3, 8 and 9). What follows is what is not done.

## Provenance of the Lean translations

The theorem is about Lean definitions that Charon and Aeneas produced from the
frozen Rust, and a reader is entitled to ask whether the committed Lean really
is what those tools produce from that source. Many of the committed
translations have no receipt tying them to an archived input, so the question
is being answered definition by definition: the tools are run again on the
frozen source, in the configuration originally used, and each fresh translation
is proved equal to the committed one. In the theorem's dependency cone there
are 1,707 translated definitions. 993 are settled: 920 are proved equal to a
fresh translation of the frozen source, and 73 are reproduced from archived
input that is itself shown to be the frozen source. 649 are not: 466 have no
fresh translation yet, most because the tools do not yet produce one in the
right configuration, and 183 are reproduced from archived input whose own
revision has not been tied to the frozen source. That last group is where the
committed Lean came from throwaway copies: when the tools could not handle a
crate whole, the function in question was copied into a small crate of its own
or written out by hand, translated or proved there, and the revision was
recorded by default rather than derived. The copies are almost certainly the
frozen functions, and only 8 definitions have been found to differ textually
from a fresh translation, but almost certainly is not a proof, so each one is
being proved equal to a fresh translation in turn. Counted by statement, 114
of the 599 verified statements rest only on settled definitions and 453 reach
one that is not yet settled; an earlier figure of 180 counted archived input
as settled and is withdrawn. Every one of these equality proofs has been
recompiled, unchanged, in the cold-rebuilt closure that the theorem itself
was checked in, so the provenance proofs and the theorem now live in one set
of compiled objects. Two genuine differences between committed and
fresh translations have turned up, and both have been settled as harmless: the
loop that shifts a transport row is proved to give the same result wherever
the verifier can reach it, and the conversion of a shift amount is proved equal
to Rust's own wrapping shift in the configuration that is deployed. The
hand-written Lean models of library code, among them the Solana SDK's key and
hash types and the core slice iterators, are now accepted as named trust rows,
following the owner's ruling of 10 November that Aspis's own code is proved and
everything outside it is trusted by a named row with a precise statement. The
six top verifier bodies, which are the two stages, the candidate preparation
and first transaction, the second transaction and the public-preparation
transcript, now each have an equality with a fresh extraction stated for
arbitrary callees, with its hypotheses shown satisfiable; the next round
discharges those callee bindings against the deployed operations. The item is
finished when every translated definition the theorem reaches is either
reproduced or proved equal; any definition left without that keeps the
statements that use it conditional. (Section 7, items 14 and 14b; section
4.7a.)

## Checked versus wrapping arithmetic

The translations were made with Rust's overflow checks switched on, so in the
Lean every integer operation either gives the true result or fails, whereas the
deployed program is built with the ordinary release profile, in which
arithmetic wraps. The theorem is therefore about the checked program, and to
carry it over to the binary one has to show, on every path the verifier takes,
that no checked operation can fail, so that the two agree. All 197
definitions in the theorem's cone that execute checked arithmetic are now
settled: 73 cannot fail on any input, 52 have a single bounded increment or
bounds-checked read as their only checked operation, and for 72 the condition
that rules out overflow is proved from their callers, among them `binary_step`,
the step of the Merkle traversal that had been the one place where a concrete
way for the two semantics to part was identified; its traversal invariant, that
the position never passes the number of nodes, is proved on every reached
state, so the unguarded length difference never wraps there. The last two
joined on 10 November: `weights.field`, whose index is proved below 64 at
every executed call, and `r24_canonical_mul`, a helper whose sixteen limb
products, squared modulus and reduction steps are each proved to succeed on
every input, every addition and subtraction in it being a wrapping one. No
verified statement now depends on an open arithmetic definition. No input on which
the wrapping binary accepts while the checked model rejects is known anywhere.
What is left on this item is not arithmetic: seven places where the
count relied on reading the source rather than on a Lean statement, such as
that a call site is read once or that a list of checked operations is complete.
Each is named for review, and the item is finished when each has become a Lean
statement or the owner has accepted it by name. One of the 197, the helper
above, also has no counterpart in the frozen source and is counted separately
under provenance. (Section
4.4, row R22; section 6, item 16.)

## A run that meets the hypotheses

A theorem whose hypotheses can never be met says nothing, so the release needs
a witness: a real run that satisfies the theorem's description of a run. From
the transfer recorded on devnet on 10 November, Lean now proves that the game
frame, the trace association, both outputs, both entrypoint admissions, the
persistence of state between the two transactions, the query bound and the
retained trust facts are exactly the recorded physical facts, rather than
something that could never hold. What remains is stated exactly by one theorem:
the trace itself, the acceptance and output of the first transaction, and the
acceptance of the second, all of which need the reference verifier's
acceptance of the recorded bytes. That became possible once the host model was
moved to the deployed program addresses, described next. The first step is a
computable version of the host, since the host's SDK and reference models are
noncomputable, and that work is under way; after it the acceptance is shown
either by an executable check or by evaluating each call symbolically with the
oracle fixed to the run's own table of queries. (Section 6, item 5; section 7,
item 19.)

## The host model at the deployed addresses

Until 10 November the host model under the theorem carried the program address
of the July 2026 V7 devnet verifier and placeholder addresses for the pool and
registry, so as written it would have rejected every recorded run of the
current version. A walk over the rebuilt closure found 718 of its 146,554
reachable constants depending on those three addresses; each was cloned with
the addresses of the 10 November deployment, the verifier `GqZzWuGT…`, the pool
`37hdATMk…` and the registry program `9pWwAcBg…`, and sent to the kernel with
full checking, 717 of them going through with their original proofs and one, a
comparison of first bytes, restated. The two verified statements that compare
addresses were proved for arbitrary addresses. The resulting theorems have the
same kernel statements as before apart from the host constants that carry the
addresses, use only the standard axioms, and have been replayed independently
by Lean's separate checker, `leanchecker`; a second instance at the 29 October
addresses exists as well. The 10 November instance is the one the release
credits, and with its replay done this item needs nothing further of its own;
it counts towards the claim through the witness of the previous paragraph.
(Section 6, item 5; section 7, item 19.)

## The pool boundary

The theorem proves nothing about the pool program. It takes, as part of its
description of a run, that every action in the recorded transaction lineage
that is not the verifier's is what the pool and the runtime did, so settlement
itself is outside it. The owner has still to decide between bringing the pool's
execution inside the security game, which would mean proving the association
between the verifier's result and the pool's use of it, and stating the claim
as conditional on that association. Once the decision is recorded, the item is
finished either with that proof or with the condition named in the claim's
first sentence. (Section 5; section 6, item 11.)

## Repeated attempts

Within one run of the experiment, repeated attempts are fully covered: the
query budget counts every hash query the adversary makes, duplicates and the
queries made before a rejection included, across both transactions. Across
separately submitted spend attempts no theorem yet states a bound. A compiled
stand-in, `RSL.MAT.campaign_charge`, gives the natural form, a sum of the
per-attempt bounds in which each attempt is charged for the verifier's hash
calls in the earlier attempts, at most 2,322 for each, with a factor of two
because the current adversary recomputes its first phase in its second; its
three obligations at the host are not yet discharged. Whether the campaign
figure is published in these units, with the verifier's own hashing charged to
the attacker's count, is a decision for the owner about the contract rather
than a question of proof. The item is finished when the reduction is proved at
the host and its units approved, or when the claim is worded per attempt only.
(Section 3.5; section 6, item 13.)

## Trust rows awaiting confirmation

The trust inventory has now been reconciled one to one with the rebuilt
closure: every row the theorem reaches has a removal condition, so does each of
the 36 reviewed transcriptions that previously lacked one, and rows the theorem
does not reach are marked as such. That reconciled table is section 4 of the
status document; the separate [`TRUST-INVENTORY.md`](TRUST-INVENTORY.md) in this
folder was taken before it, at `07123926e88`. What is outstanding is
confirmation. The owner has still to confirm or reject five rows about the
Solana runtime (`RuntimeClockSlotBinding`, `RuntimeReturnDataClear`,
`RuntimeEntrypointAdmission-Pool`, `RuntimeCpiAccountView` and
`FixturePdaRuntime`) and the reviewed transcriptions added under the owner's
standing delegation, and each proposed row has still to be classified as a
trust row, a proof task or discharged. The item is finished when every row is
confirmed, or is named in the claim as unconfirmed. (Section 4; section 6,
item 10.)

## One library panic path

One panic in the Rust standard library, the runtime-formatted message raised
when a `RefCell` that is already mutably borrowed is borrowed again
(`core/cell.rs:898`), is a form the tools do not support, and neither its
reachability in production nor its exclusion is proved. It can only abort a
transaction. Soundness is a statement about accepted runs, and an abort cannot
make a false spend accepted, so this is a question of liveness rather than
soundness, and no credit is taken for it either way. The item is finished with
a proof that the path is unreachable, a record that it is reachable, or the
liveness caveat stated in the claim. (Section 5; section 6, item 12.)
