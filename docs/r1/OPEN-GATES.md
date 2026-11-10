# What remains before the soundness claim

The claim to be made for the current version is that its spend path, as it
actually runs, has 100-bit classical soundness per attempt, with no
proof-of-work or grinding credit. The protocol's soundness is proved in Lean,
with the bound stated in [`TOP-THEOREM.md`](TOP-THEOREM.md), and this page sets
out what still stands between those theorems and the claim about the deployed
version. Until every item below is finished, that claim is not made.

A good deal is already done. The two theorems compile with only Lean's three
standard axioms. The whole closure, 14,101 modules, has been rebuilt cold from
committed sources and both theorems re-checked on the rebuilt objects alone.
Both release ELFs have been rebuilt byte for byte from the frozen source. An
axiom audit of the rebuilt closure finds 105 nonstandard axiom declarations in
it, none of them reachable from either theorem. What follows is what is not
done.

## Provenance of the Lean translations

The theorems are about Lean definitions that the Charon and Aeneas tools
produced from the frozen Rust, and a reader is entitled to ask whether the
committed Lean really is what those tools produce from that source. Many of the
committed translations have no receipt tying them to an archived input, so the
question is being answered definition by definition: the tools are run again
on the frozen source in the configuration originally used, and each fresh
translation is proved equal to the committed one.

On 10 November 2026 (research commit `9fb1e206d7d`) the theorems' dependency
cone held 1,707 translated definitions. Of these, 1,150 were settled, meaning
they are proved equal to a fresh translation of the frozen source or reproduced
from archived input shown to be that source, and 428 were not yet settled, most
because the tools do not yet produce a fresh translation in the right
configuration or because the archived input has not been tied to the frozen
source. The remaining 129 are related to the frozen source in a weaker way that
is recorded but not counted as settled, for instance an equality that holds
only on the domain the verifier uses, one that rests on a named assumption about
the standard library, or a type related to its fresh counterpart by a proved
isomorphism. Counted by statement, 122 of the 599 verified statements rest only
on settled definitions. These figures move several times a day, and from now on
only the output of the counting script is cited.

The unsettled group includes the places where the committed Lean came from
throwaway copies. When the tools could not handle a crate whole, the function
in question was copied into a small crate of its own or written out by hand,
translated or proved there, and the source revision was recorded by default
instead of being derived. The copies are almost certainly the frozen functions,
but that is not a proof, so each is being proved equal to a fresh translation
in turn. Every equality proof so far has been recompiled, unchanged, in the
cold-rebuilt closure in which the theorems themselves were checked, so the
provenance proofs and the theorems live in one set of compiled objects.

About a dozen verifier functions cannot be translated by any version of the
tools tried so far, because they use early returns or breaks inside loops,
function-pointer types or a borrow join that the translator does not support.
These are limits of the translation tool and say nothing against the code. They
stay open obligations and are not turned into trust assumptions. Work on the
translator itself is now funded, so these functions are an open obligation with
a route to closing it
and not a permanent exclusion.

Two genuine differences between committed and fresh translations have turned
up, and both have been settled as harmless. The loop that shifts a transport
row is proved to give the same result wherever the verifier can reach it, and
the conversion of a shift amount is proved equal to Rust's own wrapping shift
in the deployed configuration. The hand-written Lean models of library code,
among them the Solana SDK's key and hash types and the core slice iterators,
are accepted as named trust assumptions. The rule is that Aspis's own code is
proved and everything outside it is trusted through a named assumption with a
precise statement. The six top verifier
bodies (the two stages, the candidate preparation and first transaction, the
second transaction and the public-preparation transcript) each have an equality
with a fresh translation stated for arbitrary callees, with its hypotheses
shown satisfiable. Several of those callee bindings are now discharged against
the frozen code, among them both stages' hash and mark slots, the field decode
on its window, the checkpoint readers, five adapter slots and the two
first-stage decoders on their domain, and the rest are in progress.

The item is finished when every translated definition the theorems reach is
either reproduced or proved equal. Any definition left without that keeps the
statements that use it conditional.

## Checked versus wrapping arithmetic

The translations were made with Rust's overflow checks switched on, so in the
Lean every integer operation either gives the true result or fails, whereas the
deployed program is built with the ordinary release profile, in which
arithmetic wraps. The theorems are therefore about the checked program, and
carrying them over to the binary means showing, on every path the verifier
takes, that no checked operation can fail, so that the two agree.

All 197 definitions in the theorems' cone that execute checked arithmetic are
now settled. For 73 no operation can fail on any input, 52 have a single
bounded increment or bounds-checked read as their only checked operation, and
for 72 the condition that rules out overflow is proved from their callers.
Among the last is the step of the Merkle traversal, which had been the one
place where a concrete way for the two semantics to part was identified; its
invariant, that the position never passes the number of nodes, is proved on
every reached state, so the unguarded length difference never wraps there. The
final two to join were the weights lookup, whose index is proved below 64 at
every executed call, and a multiplication helper whose sixteen limb products,
squared modulus and reduction steps are each proved to succeed on every input.
No verified statement now depends on an open arithmetic definition, and no
input is known on which the wrapping binary accepts while the checked model
rejects.

What is left here is not arithmetic. There are seven places where the count
relied on reading the source instead of on a Lean statement, such as that a
call site is read once or that a list of checked operations is complete. Each
is named for review, and the item is finished when each has become a Lean
statement or has been accepted by name as an assumption. The multiplication helper above has
since been proved equal to the frozen field multiplication on its guarded
domain, and is counted under provenance in the weaker column described there.

## A run that meets the hypotheses

A theorem whose hypotheses can never be met says nothing, so the release needs
a witness, a real run that satisfies the theorem's description of a run. From
the transfer recorded on devnet on 10 November 2026, Lean proves that the game
frame, the trace association, both outputs, both entry-point admissions, the
persistence of state between the two transactions, the query bound and the
retained trust facts are exactly the recorded physical facts. What remains is
stated exactly by one theorem: the trace itself, the acceptance and output of
the first transaction, and the acceptance of the second, all of which need the
reference verifier's acceptance of the recorded bytes.

There is now executable evidence for this. A computable copy of the host model
at the deployed addresses, each copied definition proved equal to the
original, ran both transactions of the recorded transfer in Lean's interpreter,
and both were accepted; the first transaction's reference value, evaluated the
same way, equals the recorded checkpoint. The second transaction's reference
value could not be evaluated within the resource limits and is not
established: the interpreter timed out, and a native build would need the whole
dependency cone compiled to machine code. This is an executable check and not a
proof, so it does not by itself discharge the four remaining facts. Running the
model's own entry point at kernel level is blocked by two places in the model
that would need restating. How to treat them is undecided. The likely course is
for this item to rest on the executable evidence together with the proved
equivalence for the first stage that the reference value feeds, with a
restatement only if a reviewer requires a kernel-level witness.

## The host model at the deployed addresses

Until 10 November 2026 the host model under the theorems carried the program
address of the July 2026 V7 devnet verifier and placeholder addresses for the
pool and registry, so as written it would have rejected every recorded run of
the current version. A walk over the rebuilt closure found 718 of its 146,554
reachable constants depending on those three addresses. Each was cloned with
the addresses of the 10 November deployment, the verifier `GqZzWuGT…`, the pool
`37hdATMk…` and the registry program `9pWwAcBg…`, and sent to the kernel with
full checking; 717 went through with their original proofs and one, a
comparison of first bytes, was restated. The two verified statements that
compare addresses were proved for arbitrary addresses.

The resulting theorems have the same kernel statements as before apart from
the host constants that carry the addresses, use only the standard axioms, and
have been replayed independently by Lean's separate checker, `leanchecker`. A
second instance at the 29 October addresses exists as well. The 10 November
instance is the one the release credits, and with its replay done this item
needs nothing further of its own; it counts towards the claim through the
witness of the previous section.

## The pool boundary

The theorems prove nothing about the pool program. They take, as part of the
description of a run, that every action in the recorded transaction lineage
that is not the verifier's is what the pool and the runtime did, so settlement
itself lies outside them. There are two ways to close this. One is to bring the
pool's execution inside the security game, which means proving the association
between the verifier's result and the pool's use of it, and the other is to
state the claim as conditional on that association. The choice has not been
made, and the item is finished either with that proof or with the condition
named in the claim's first sentence.

## Repeated attempts

Within one run of the experiment, repeated attempts are fully covered, since
the query budget counts every hash query the attacker makes, duplicates and the
queries made before a rejection included, across both transactions. Across
separately submitted spend attempts no theorem yet states a bound. A compiled
stand-in theorem gives the natural form, a sum of the per-attempt bounds in
which each attempt is charged for the verifier's hash calls in the earlier
attempts, at most 2,322 for each, with a factor of two because the current
attacker model recomputes its first phase in its second; its three obligations
at the host are not yet discharged. Whether the campaign figure is published in
these units, with the verifier's own hashing charged to the attacker's count,
is a decision for me about the contract and not a question of proof.
The item is finished when the reduction is proved at the host and its units
approved, or when the claim is worded per attempt only.

## Trust assumptions awaiting confirmation

The trust inventory has been reconciled one to one with the rebuilt closure.
Every assumption the theorems reach has a removal condition, so does each of
the 36 reviewed transcriptions that previously lacked one, and assumptions the
theorems do not reach are marked as such. That reconciled table is in
[`SOUNDNESS-STATUS.md`](SOUNDNESS-STATUS.md), Appendix F; the separate
[`TRUST-INVENTORY.md`](TRUST-INVENTORY.md) in this folder was taken before it.

Since 10 November 2026 no trust assumption is accepted unless it is a standard
Solana runtime or Rust library operation. Under that rule the
transcription of the public-preparation accessor was withdrawn as a trust item;
its proofs stay as evidence, the newer tool now translates the function, and
it is proved equal to its fresh translation with no assumption named. The
transcription of the compiler-derived clone and equality operations on the
field types stays, since those are compiler derives, and the deployment-id
constant entered the SDK assumption with a receipt comparing it byte for byte
with the deployed ELF. The reviewed transcriptions of Aspis code fall under the
same rule, including those accepted earlier, on 27 October 2026. Each is an
open obligation and not an assumption, to be discharged by a translation proved
equal, and until then the statements that use it are conditional.

Five assumptions about the Solana runtime are still provisional. They cover the binding of the clock reading
to the bank slot, the clearing of return data, the admission of the pool's
entry point, the view of accounts after a cross-program call, and the address
derivation used for test fixtures (`RuntimeClockSlotBinding`,
`RuntimeReturnDataClear`, `RuntimeEntrypointAdmission-Pool`,
`RuntimeCpiAccountView` and `FixturePdaRuntime` in the inventory). Each proposed
assumption has also still to be classified as a trust assumption, a proof task
or discharged. The item is finished when every one is either confirmed or named
in the claim as provisional.

## One library panic path

One panic in the Rust standard library, the runtime-formatted message raised
when a `RefCell` that is already mutably borrowed is borrowed again
(`core/cell.rs:898`), is a form the tools do not support, and neither its
reachability in production nor its exclusion is proved. It can only abort a
transaction. Soundness is a statement about accepted runs, and an abort cannot
make a false spend accepted, so this is a question of liveness, and no credit
is taken for it either way. The item is finished with a proof that the path is
unreachable, a record that it is reachable, or the liveness caveat stated in
the claim.

## Where this comes from

The provenance figures are those of research commit `9fb1e206d7d` on
10 November 2026. Everything else on this page comes from the status document
on the [`research`](https://github.com/DJBarker87/aspisZK/tree/research) branch
at commit `90795727483`, which [`SOUNDNESS-STATUS.md`](SOUNDNESS-STATUS.md) in
this folder is written from. The details behind each item are in the following
places there.

| Item | Status document |
| --- | --- |
| Provenance of the Lean translations | section 7; Appendix H, items 13 and 14 |
| Checked versus wrapping arithmetic | Appendix F, translation table; Appendix G, item 16 |
| A run that meets the hypotheses | Appendix G, item 5; Appendix H, item 19 |
| The host model at the deployed addresses | section 7; Appendix H, item 19 |
| The pool boundary | section 5; Appendix G, item 11 |
| Repeated attempts | section 3.5; Appendix G, item 13 |
| Trust assumptions awaiting confirmation | section 4; Appendix F; Appendix G, item 10 |
| One library panic path | section 5; Appendix G, item 12 |
| Work already done | Appendix G, items 3, 8 and 9 |
