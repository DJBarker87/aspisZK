# Soundness claim for the verifier spend path

This is the soundness claim to be published for the current version of
Aspis once the remaining release items are finished, written out with its
complete status. It gives the theorem in prose and in Lean, every binder and
retained hypothesis, the exact bound and the range in which it holds, the trust
the theorem rests on, what it does not claim, and what remains. It is a draft in
one specific sense: the protocol's soundness is proved in Lean, with the bound
stated below, but the claim about the deployed version is not made until every
item of section 6 has its evidence. The items still open are summarised in
[`OPEN-GATES.md`](OPEN-GATES.md).

In outline, the theorem considers an arbitrary adaptive attacker that queries
SHA-256, modelled as a random oracle, as often as it likes, and then submits
the two transactions of a spend. If the runtime executes them as the approved
two-transaction game and both are accepted, the theorem bounds by total(Q) the
probability that the acceptance is a false spend, where Q counts every hash
query the attacker makes. For any feasible Q the bound is about
(Q+34)·2^-105.09, and it is at most (Q+1)·2^-100 for Q up to about 2^152.37.
The theorem holds about the frozen verifier source, as translated into Lean, in
its deployed configuration, under a small set of named assumptions about the
Solana runtime, the SDK, the Rust standard library and the tools, which are set
out in section 4.

What stands between this and the release claim is chiefly three things. Every
committed Lean translation must be tied to a fresh translation of the frozen
source; a handful of review items remain on the bridge between the checked
arithmetic of the translations and the wrapping arithmetic of the deployed
binary; and the pool's actions are taken as given in the theorem's game, so I
must decide whether to bring the pool inside the proof or state the claim as
conditional on it. Smaller items concern a witness run, repeated attempts,
confirmation of some trust assumptions and one library panic path.

The sections below follow the order of the original document. Each leads with
the main ideas in prose; tables and the full Lean statements are in the
appendices at the end.

## 0. Where things stand

The function ledger records all 599 spend-path statements as closed, none
qualified and none open. The top-level theorem is assembled unconditionally at
the corrected host model: the two host theorems, `deployed_splitB` and
`deployed_charge`, compile in one combined import with every interface field
filled by a delivered closed term, so no field is a hypothesis or a placeholder.
The whole dependency closure has been rebuilt cold from committed sources and
both theorems re-checked on the rebuilt objects; both release ELFs have been
rebuilt byte for byte from the frozen source; and an axiom audit of the rebuilt
closure finds only the three standard axioms reachable from either theorem.

The non-vacuity item is partial, now with executable evidence, and the
remaining release items of section 6 are open. The provenance of the Lean
translations is still a release blocker.

## 1. The theorem as it will stand

### 1.1 In words

Fix the frozen verifier implementation, that is `crates/`,
`programs/r1-cost-probe` and `Cargo.lock` at revision `4bb3b3f`, in its
deployed configuration, with the owned first- and second-stage bodies taken at
their models. Model SHA-256, as invoked through the runtime's hash syscall, as a
uniformly random function H from byte strings to hash states. Let `a` be an
arbitrary two-phase adaptive adversary, and let `a⊤` be `a` with both of its
allocator-state outputs set to success, which is the adversary that actually
reaches the verifier. Suppose that, for every oracle H, the hash queries `a⊤`
issues across both phases, counting duplicates and every call issued before a
rejection, number at most Q = Q0 + Q1.

For each H, the deployed pair of transactions is defined as what `a⊤` actually
outputs at H, so the attacker's choice of what to submit is part of its own
charged computation. Suppose further that the Solana runtime executes these two
entries as the approved two-transaction game: consecutive executions on one
bank lineage, the same physical checkpoint account named by both with nothing
touching it in between, the first transaction's parent status success, and the
recorded checkpoint actions equal to the physical runtime actions, all under the
retained runtime, SDK and standard-library assumptions.

Then three things hold. The first holds independently of H, and the second and
third at every H.

1. The model's failure probability, which is an average over H, is at most
   total(Q). If Q is at most the maximum given in section 3.2 it is at most
   (Q+1)·2^-100, and if Q = 0 it is below 2^-100 with an exact margin.
2. All the other parts of the earlier adopted headline theorem except its
   fourth hold unchanged: the boundary, driver and SDK equalities, the three
   spend claims, the copy facts, the event facts, the checkpoint protection,
   the trace and recorder facts, and the installation of the code.
3. Either the headline's fourth part, its outcome statement, holds with its bad
   event retargeted to the collision event of the attacker's own run, or that
   collision event occurs at H.

The collision event (E_rec) is a collision among the hash reads recorded during
the attacker's own run, capped at Q + 2,965 reads. It is already charged inside
the failure probability, so the third conclusion adds nothing to the bound.

The failure the bound counts is an accepted run in which the knowledge
extractor returns nothing, plus a small term for the extractor's query scan
running out. How the extracted witness is tied to the spend relation has not
been re-audited for this draft, and the final statement audit must confirm it
before the claim is described as "acceptance implies a valid spend witness
except with probability total(Q)".

Averaged over all oracles, with no conditioning and no oracle excluded, the
intended statement is that the per-attempt failure indicator has mean at most
total(Q), with the collision event charged once. The second host theorem
delivers this as two separate facts: oracle by oracle, a failing accepted run
lies in the collision event of one fixed recorder program, and that event's
mean is bounded. It does not itself state the failure indicator's expectation
as a single program mean. That the collision event is charged only once is
established in compiled Lean for the model's failure probability; for the
per-attempt event including the outcome statement it rests on a lemma proved at
the level of the generic stand-in.

### 1.2 The Lean form

The theorem is built in two layers. A generic stand-in layer proves the shape
of the argument over abstract interface structures, with every headline object
a field of a structure and never an axiom or an opaque constant; it compiles
with only the standard axioms. The host layer then instantiates every interface
field with a delivered closed term about the actual translated code, giving the
two host theorems whose printed statements are reproduced in Appendix A and in
[`TOP-THEOREM.md`](TOP-THEOREM.md).

Inside the proof, the condition that the submitted pair is the adversary's
output holds by construction at every oracle, so it filters nothing and is not a
hypothesis of either theorem. The averaging at the host is done by a pointwise inclusion, shown in
Appendix A, followed by a bound on the recorder program's mean and the existing
chain bounding the failure probability. Both events live on the same space of
oracles, and the adversary's randomness is part of the adversary program.

`#print axioms` and an independent walk of the proof terms give exactly
`propext`, `Classical.choice` and `Quot.sound` for both theorems, whose
dependency cones hold 146,370 and 146,551 constants.

The stand-in takes 22 interface structures besides the libraries, the account
counts, the execution instance and the context. In the final theorem each must
be a delivered closed term of exactly its type, never a hypothesis, `sorry`,
variable or trust assumption, and at the seventh assembly run every one is. How
each is delivered is listed in Appendix B.

### 1.3 Binders that are instantiated

The earlier adopted headline theorem had many universally quantified binders on
the model side. In this theorem some of them are instantiated, each by
substitution proved by `rfl` or a named lemma, and none of the substitutions is
a hypothesis or a trust assumption. The native stage functions become their
models. The allocator states are set to success, because an actual run that
returned successfully had every allocation succeed, a failed allocation
aborting the program. The adversary is replaced by its normalised form `a⊤`,
since allocation success is something the deployed attacker does not control,
while `a` itself stays universal. The submitted pair becomes the adversary's
output at H. The hash function is instantiated as the only total adapter the
syscall assumption admits. The environment's missing pieces are filled with the
corrected host seed described in section 2, and the first stage's allocation
stream is fixed as statement data. Appendix C gives the full table.

### 1.4 Binders and hypotheses that are retained

The two host theorems bind slightly different things. `deployed_splitB` binds
the world and transaction types, the SDK library model with its borrowing
assumption, the slice copy with its standard-library assumption, the four
allocation streams of the second stage, the fixed experiment data (including
the adversary), a world, an oracle, the query budget and the description of the
run. `deployed_charge` binds the same except that it has no run, no single
world and no top-level oracle: the oracle is bound inside each conjunct, the
world is an arbitrary function of the oracle, and the description of the run
appears only inside the failure indicator being averaged. So the description of
the run, the two entry-point admissions and the persistence assumption are
hypotheses of `deployed_splitB` only, and parts of the averaged event in
`deployed_charge`.

Of the retained items, the SDK borrowing assumption and the standard-library
assumption are trust; the two entry-point admissions and the persistence
assumption are trust stated as facts of the actual run's world; the query
budget is a parameter of the statement, the Q of the bound, and is not
discharged; the two-transaction game is the statement of the approved
experiment; and the success of both transactions is the attack's success
antecedent. Everything else is universally quantified data. Two components of
the fixed data, the program-address derivation and the clock reply, are new
universal data with no counterpart binder in the headline; they were previously
inside the universal environment, and being universal they restrict nothing.
The query bound must hold for every pair of an environment digest and a query
oracle. Appendix D gives the full table.

The final theorem was required to contain no hypothesis about the root digest
(Root0), no hash-injectivity premise, no premise that the pair realises the
adversary's choice, and no new trust assumption. The audit of the printed
statements confirms each of these in writing, together with the facts that the
adversary is universal and never a constant and that the averaging conditions
on nothing.

## 2. Before and after, against the adopted headline

The earlier adopted headline theorem had every binder independent and
universal, including the submitted pair, which was not tied to the adversary;
the only link was the query bound. In the new theorem the adversary stays
universal, while the pair is no longer quantified but defined as the
adversary's execution output at H, and the model-side binders listed in
section 1.3 are instantiated. The per-world binders stay universal and may
depend on H arbitrarily.

The effect is that the new theorem covers fewer free instantiations of
model-side binders, each justified as a substitution, and covers the adaptive
case that the old theorem did not connect to the bound: a pair chosen after
querying H is a charged part of the adversary. At each H, every pair the old
statement covered is also covered, because a constant adversary realises it
with zero queries. The universal statement is nevertheless a different theorem
and should not be read as a weakening of the old one, because the pair is now
bound to the adversary's run.

The carriers are unchanged apart from the allocator state type becoming a
boolean and actual-code carriers being added and related to the headline
carriers. Four former hypotheses (extraction, the two acceptances and the game)
are now derived. The description of the run is added; since the game was itself
a binder before, this re-expresses the game on the actual images together with
the actual success results and is not a new kind of assumption. The earlier
realisation hypothesis approved on 7 November is discharged by construction.
The query bound, both admissions, persistence, the SDK assumption, the
standard-library assumption and the copy are unchanged. The ideal-oracle
realisation and the syscall assumption are no longer Lean premises at the top,
because they are instantiated, but they remain the justification for reading
the run's hash replies as values of H.

The failure event of the probability statement, an accepted run whose extractor
returns nothing plus query-scan exhaustion, is unchanged. The headline's fourth
conjunct used a collision event on a fixed-selection program; the new theorem
replaces it with the outcome statement or the collision event of the
adversary's own run. The form of the event is the same, but it is evaluated on
the adversary's own run, and it is exactly the event the failure probability
already charges, so no new term enters the bound. Off that event the new form
gives exactly the headline's shape; on it the outcome statement is lost, and
those worlds are already paid for. The averaged statement `deployed_charge` is
new.

The retained premises are satisfiable: a constant adversary realises any pair,
and the description of the run holds of any actual accepted pair. That the
physical predicates of the game and the trace are not false is the non-vacuity
item of section 6.

## 3. The numeric claim

### 3.1 The exact bound

The bound is defined in Lean as follows.

```
total(Q) = (Q+34)·B + collisionLoss(Q) + accountLoss(Q) + 2^-126 + 2^-454
B                = PerAttemptEnvelope.B = 15/2^109            (≈ 2^-105.093)
collisionLoss(Q) = 6·(Q+1161)^2 / 2^256
accountLoss(Q)   = 6·(Q+2965)^2 / 2^256
```

Q is the number of hash queries issued by the adversary across both phases,
counting duplicates and every call issued before a rejection, taken on `a⊤`.
Every term is listed in Appendix E, and nothing else enters. In words, the
first term charges every fresh transcript start, among the adversary's Q
queries and the 34 starts the submitted transcript reads before terminal
authentication, with probability at most B; the two squared terms are the
collision mass over the verifier's first reads and over the reads recorded in
the adversary's own run; 2^-126 allows for the extractor aborting; and 2^-454
for the query scan running out.

### 3.2 The per-attempt corollary and its valid range

Lean proves that total(Q) ≤ (Q+1)·2^-100 holds exactly when Q is at most

maxQueries = 7388980242446479800895501321004157112314840375 ≈ 2^152.372.

Above maxQueries the bound total(Q) still holds, but the (Q+1)·2^-100 form does
not. A script reproduces maxQueries from exact rationals. Under the option I
chose on 7 November 2026 the number and the range are unchanged; the
alternative would have needed a second collision charge, with range about
2^151.787, and is not used.

The form (Q+1)·2^-100 is a corollary of total(Q) and is not itself the
contract, whose binding criteria are these two.

- **(A), the whole experiment with no adversary queries.** Lean proves the
  exact margin 2^-100 − total(0) = 2^-108 − 6·(1161² + 2965²)/2^256 − 2^-126 −
  2^-454 > 0. Numerically total(0) ≈ 0.99609·2^-100 ≈ 2^-100.0056, with a margin
  of about 0.999996·2^-108, and almost all of total(0) is the 34 transcript
  starts.
- **(B), with the dependence on Q kept.** For 0 ≤ Q ≤ maxQueries the failure
  probability is at most total(Q), which is approximately (Q+34)·2^-105.093 for
  every Q below about 2^100. The (Q+1)·2^-100 figure is looser than total(Q) by
  a factor of 2^5.093 (log2 of 512/15) for Q above about 10^4, and by about
  2^4.9 near Q ≈ 233.

No proof-of-work or grinding credit is used, no probability is divided by
adversarial work, and no work-normalised figure is stated.

### 3.3 Query accounting

What is counted is the chronological list of hash calls the induced prover
issues across both phases, duplicates and every call before a rejection
included, which is identified with the length of the oracle program's query log.
The constants 34, 1,161, 1,921 and 2,965 in the bound are verifier envelopes
charged on top of Q, and the issued-call log is at most Q + 2,322. Because the
submitted pair is the output of `a⊤`, every query used to choose it is in Q.

The count is taken on `a⊤` and not on `a`. Where `a` would report a failed
allocation, the wrapper fails before the native call, so `a⊤` can issue more
verifier calls than `a`. This does not affect soundness, but the published Q
must be described as the count of `a⊤`.

### 3.4 Why adaptive selection is covered

Before the current form, the charged event used a constant selector on a pair
quantified independently of the adversary, and if the pair may be an arbitrary
function of H, the probability of that event can be 1 (a pigeonhole argument,
not checked in Lean). The current form removes this gap by construction. The
pair is `a⊤`'s output at H; the collision event is evaluated on `a⊤`'s own run
with a selector that depends on its output; the account-mass lemma holds for
any selector applied to the source's own output and is already charged; and
Lean proves that at every H a successful actual run whose outcome statement
fails lies in the collision event at the same H. The inclusion is proved, not
assumed, and it concerns the actual adversary's execution.

### 3.5 Repeated attempts

Within one experiment repeats are covered. The query budget counts every issued
call, duplicates and rejected prefixes included, across both phases, so an
adversary that tries many candidate transcripts offline before submitting is
charged for every query it makes. That is the random-oracle work metric of the
contract.

Across separately submitted spend attempts no theorem in the dependency closure
states a bound. The contract says such campaigns are accounted for by the
per-attempt bound, in the per-experiment form (B). The natural reduction treats
attempt i as an instance of the theorem with an adversary that runs everything
up to and including attempt i; the world binders are arbitrary, so earlier
chain state is covered; that adversary must reproduce the verifier's hash calls
of earlier attempts as its own queries, at most 2,322 per attempt; and a union
bound then gives a probability of some attempt being accepted with failure of
at most the sum of total(Q_i).

A compiled stand-in theorem corrects this sketch: Q_i is the cumulative
issued-call count of the reduction adversary, at most c times the attacker's
own queries up to attempt i plus 2,322 for each earlier attempt, with c = 2 for
the current adversary type because its second phase recomputes its first and it
carries no private state; c = 1 would need a host argument. Its three host
obligations are not discharged: constructing the reduction adversary with the
submitted inputs as its outputs at every H, bounding its cost, and showing that
whatever the campaign adversary sees between attempts is a function of H and of
data fixed before H. That last obligation does not restrict what the attacker
may observe or adapt to; it is a cost-accounting rule that charges the
verifier's hash calls of earlier attempts to the reduction adversary's count.
That is the work performed through verifier interactions that the contract
must state explicitly, and whether the campaign corollary is published in these
units or campaign security stays stated per attempt only is a decision for me
on the contract's scope, not a question of proof.

The sum must not be replaced by setting a single-experiment bound to 1. If the
reduction is not accepted, the published claim must say that campaign security
is stated per attempt only.

### 3.6 What the number applies to

The number bounds the per-attempt failure of the two-transaction spend
experiment: the attack succeeds at H and either the extractor fails or the
outcome statement fails. It applies under the trust inventory of section 4, at
the frozen source and configuration of section 1.1. It says nothing about
privacy, pool settlement, double spending, custody or availability (section 5).

## 4. The trust the theorem relies on

The trust boundary is the frozen Aspis source. Aspis's own code is proved, and everything outside it, meaning the Rust
core, alloc and std libraries, the Solana SDK crates, the compiler and linker
and the runtime syscalls, is trusted through a named assumption with a precise
statement and is not proof work. No trust assumption is accepted unless it is a
standard Solana runtime or Rust library operation.
Under that rule the transcription of the public-preparation accessor was
withdrawn as a trust item (its proofs stay as evidence, and the newer tool now
translates the function, which is proved equal to its fresh translation with
no assumption named), the transcription of the compiler-derived clone and equality
operations on the field types stays because those are compiler derives, and the
deployment-id constant entered the SDK assumption with a receipt comparing it
byte for byte with the deployed ELF. The reviewed transcriptions of Aspis code
are not assumptions awaiting confirmation: each is to be discharged by a translation
proved equal, and until then the statements that use it are conditional.
The rule covers the transcriptions accepted earlier, on 27 October 2026, as
well, so those too are open obligations and the statements that use them are
conditional until a translation is proved equal.

This inventory has been reconciled one to one against the replayed proof cones
of both theorems. A Lean constant counts as reached only if it is in both cones,
and each assumption is marked with the route by which it reaches the theorems:
as a binder of the printed statement, as part of the description of the run, as
a structure built by a term at the top (when the assumption remains the
physical reading of what the term models), as a window law of the stage bodies,
through a closed ledger statement whose root is in the cones, through a frozen
function on the deployed path whose certificate root is outside the cones
(needed to read the model as the physical run, not for the Lean proof), or as
tool trust. Of the 599 closed ledger statements, 140 have a root in the cones
and 7 more enter through restated top fields; for the other 450 the closed
certificate is evidence that the Lean models describe the frozen code, and not
a dependency of the Lean proof. Assumptions the cones do not reach are kept and
marked, proposals not yet decided are listed separately, and no assumption has
been removed.

The assumptions themselves are of five kinds. The random-oracle model of
SHA-256 and the readings that connect the program's hash replies to H have no
removal condition, since they are what the random-oracle model means. The
Solana runtime is trusted at named points, some of them settled and some still
provisional. The SDK and standard library
are trusted through the account-borrowing and slice-copy assumptions that are
binders of the theorem, and, since 10 November 2026, through a set of
library-model assumptions covering the SDK's key and hash types, the core slice
iterators, cross-crate constants, Option and Result combinators, array and
slice operations, numeric and iterator models and Aeneas's discriminant
helpers. The tools, meaning Charon and Aeneas, Kani, the compiler and the pinned
libraries, are trusted at the level of trace fidelity with recorded narrowings,
and the binding to the deployed artefact is a realisation obligation discharged
only by the final audit. The reviewed transcriptions stand in for functions the
tools could not translate, and they are to be discharged as described above.

Several things in the theorem are not trust but stated parts of it: the query
budget, the two-transaction game, the success antecedent of the run, and the
allocation streams. The seven historical checkpoint interfaces are reached only
as constructed terms, built from the persistence assumption, the game and
source proofs, and are never hypotheses.

The full reconciled inventory, with the exact statement, route, removal
condition and confirmation status of every assumption, is in Appendix F. A
plain-language version taken before reconciliation is in
[`TRUST-INVENTORY.md`](TRUST-INVENTORY.md).

## 5. What is not claimed

The claim says nothing about privacy, which has its own contract, including its
side-channel scope; nothing here bears on it. It says nothing about double-spend
prevention, custody or availability, which are separate properties with their
own contracts and are not implied by soundness of acceptance. It makes no
mainnet claim, says nothing about the client and prover recipe (its features and
constant-time decoding), and gives no work-normalised or attack-cost figure.

The theorem proves nothing about the pool program. It retains, in the trace part
of the description of the run, the hypothesis that every action in the recorded
lineage that is not the verifier's is the recorded pool or runtime action, so
settlement is not covered. Whether to put the pool inside the admitted game or
to report the headline as conditional on the association with the pool as its
consumer has not been decided. If the conditional boundary is
chosen, the claim must say "conditional on the Pool consumer association" in
its first sentence, and must then also mention the pool assumptions in the
inventory.

Extraction provenance is a release blocker. No release claim may be made until
fresh translation with receipts, together with per-definition equality theorems,
covers every translation the theorem reaches, and a definition without an
equality proof keeps the statements that use it conditional. This is not a
counterexample and reopens no statement. Current figures are in section 7 and
in [`OPEN-GATES.md`](OPEN-GATES.md).

The final trust audit and the association between source and deployed ELF are
not closed. The native bridges concern the frozen Rust source as compiled for
Kani, not the deployed ELF bytes, and the pool that ran on devnet in October was
not the frozen pool.

One panic in the standard library, raised when an already mutably borrowed
`RefCell` is borrowed again (`core/cell.rs:898`), is a runtime-formatted form the
tools do not support, and neither its reachability in production nor its
exclusion is proved. It can only abort a transaction, and soundness is a
statement about accepted runs, so an abort cannot produce an accepted false
spend; but no credit is taken for reachability or exclusion.

Finally, the claim does not extend to joint real-byte non-vacuity beyond the
check of section 6, and it does not claim the deployed attribution at the five
retired preparation interfaces of the first transaction (section 7, item 9)
unless the final audit shows those interfaces are covered by native bridges.

## 6. Evidence required before the claim is made

Each item needs a committed artefact. The first four are the gate for the final
assembly of the theorem, and all four are met: the ledger has all 599
statements closed under an all-slices composition check; every interface field
is a delivered closed term; both host theorems compile in the combined import
with only the standard axioms and with complete records; and the printed
statements are quoted verbatim and audited against the old headline.

The rest are release obligations, and their state is mixed. The cold replay of
the final closure and the axiom half of the final audit are met. Non-vacuity is
partial, with executable evidence that the model accepts the recorded devnet
transfer. Provenance, the overflow semantics, the pool boundary, the trust
inventory, the panic path and campaign accounting are open in the ways
described in [`OPEN-GATES.md`](OPEN-GATES.md). Appendix G lists every item with
its requirement and status.

## 7. Uncertainties and findings

These are stated so that the published version does not inherit them silently.
The ones that matter most to a reader are these.

The count of 599 closed statements is not the size of the proof's dependency.
Of the 599, 140 have a root in the cones of the two theorems and 7 more enter
through restated top fields; the remaining 450 are proved statements about the
same code that this theorem does not depend on, and two rows record no root at
all. Nothing is contradicted, but for most rows the closed certificate is
evidence that the Lean models describe the frozen code, not a premise the kernel
checks for this theorem, and the published claim must not present the row count
as the size of the proof's dependency.

Provenance has been worked through definition by definition. On 10 November
2026 (research commit `9fb1e206d7d`), of the 1,707 translated definitions in the
theorems' cone, 1,150 were settled, 428 were not, and 129 were related to the
frozen source in a weaker way that is recorded but not counted as settled (for example an equality that holds only on the domain used,
one that depends on a named library assumption, or a type related by a proved
isomorphism; any definition proved equal through a library assumption is
counted this way and never as settled). Counted by statement, 122 of the 599
rested only on settled definitions. These figures move several times a day, and
only the output of the counting script is cited. The definitions in the weaker
group are a second barrier of their own, since settling every open definition
would by itself bring the statements resting only on settled definitions to 257
of 599. Release requires each class to be closed in its own way: conditional
bindings brought to zero, isomorphisms given proved maps, refinements on a
domain or on a loop's return given proved coverage of every call site, and
library assumptions counted only if accepted.
About a dozen verifier functions cannot be translated by any version of the
tools tried, because of early returns or breaks inside loops, function-pointer
types or a borrow join. These are limits of the translation tool and not of the
code; they stay open obligations and are never turned into trust assumptions.
Work on the translator itself is now funded, so these functions are an open
obligation with a route to closing it. The six top verifier bodies each have an equality with a fresh
translation stated for arbitrary callees, and several of those callee bindings
are now discharged against the frozen code (both stages' hash and mark slots,
the field decode on its window, the checkpoint readers, five adapter slots and
the two first-stage decoders on their domain), with the rest in progress. Along the way several earlier figures were
corrected: a source-revision field that had been a fixed default string, a
"receipted" class that had been counted as settled, and an earlier figure of
180 clean statements, which is withdrawn. Every credited provenance proof has
been replayed against the cold-rebuilt closure, and a heartbeat audit found
credited theorems elaborating under raised limits, all of which were then
recompiled at the default limit without failure.

The checked-versus-wrapping difference was found by the provenance work, which
saw fresh translations of the frozen source differ from the committed ones on
arithmetic because the historical translations ran with overflow checks on and
the deployed build does not. The committed Lean is a faithful translation under
that configuration, and the transfer to the wrapping binary is the overflow
obligation, now settled for all 197 arithmetic definitions with seven textual
review items left. The one multiplication helper among them that exists only in
the committed Lean is now proved equal to the frozen field multiplication on its
guarded domain, and is counted under provenance in the weaker column.

The cold replay found that Lean does not re-typecheck imported objects, so
neither the axiom walk nor the reference scan detects an object compiled
against a different version of an import. The cached closure held 56 such
modules; three proofs were repaired with their statements frozen, and the
differing constants lie outside both theorems' cones. The theorems are credited
on the replayed closure.

The host model under the theorems originally carried the July 2026 verifier's
address and placeholder pool and registry addresses, so it rejected every
recorded run. It has been re-instantiated at the 10 November 2026 deployment's
addresses, with the same kernel statements apart from the host constants that
carry the addresses, and that instance is the one the release credits.

The soundness and privacy theorems were found to share only the mathematical
core, and the single Rust model for both is the source that
ran on devnet: `4bb3b3f` and the pool at `b936275`. The proving client that made
the devnet proofs has been rebuilt byte for byte, but it was built from a
different client wrapper with the prover's insecure test-fixture feature
switched on and linked an earlier pool tree, so the library crates that produced
the proofs are the pin's while the client wrapper, its features and the pool
library it linked are not. Either the pin description will be amended or the
client will be rebuilt from the pin and devnet run again.

Appendix H lists every finding with its status.

## Appendix A. The Lean statements

The stand-in theorems that the host instantiates are these.

```lean
theorem RSL.TASB.top_splitB_physical {S : Sig} {R : RecSig S}
    (L : PoolLib) (D : DeployedIds) (V0 : V2Lib) (VL : VLib)
    (P : PreparedNew VL) (C : S1Lib VL) (I : Impl L V0 VL)
    (sp : Split S) (hl : Headline S) (a0 : A0_Digest S)
    (nmm : NMM_Roots L D V0 VL I) (nmx : NMX_Root L D V0 VL I) (nms : NMS_Roots L D V0 VL I)
    (nmv : NMV_Roots L D V0 VL P C I) (nmw : NMW_Roots L D V0 VL P C I)
    (nmt : NMT_Roots L V0 VL P C I) (nmp : NMP_Roots L V0 VL P I) (nmo : NMO_Root L V0 VL I)
    (nmn : NMN_Root L V0 VL I)
    (g1a : NNC_G1a S L V0 VL I) (rs : RecSelect S R) (hb : HeadlineB S R)
    (nmfB : NNC_NMFPrimeB S L D V0 VL P C I g1a R) (r0 : NNC_R0Rep S V0)
    (a1 : NND_A1 S VL P C) (a2 : NND_A2 S L D V0)
    (a3 : NNE_A3 S VL P C) (a4 : NNE_A4 S L D V0) (a5 : NNE_A5 S L V0 VL P C I)
    (count1 : ∀ c, (S.args1 c).accounts.length = 3)
    (count2 : ∀ c, (S.args2 c).accounts.length = 7)
    (X : ExecB S R) (fx : X.Fixed) (w : X.World) (H : X.Oracle)
    (queries : X.QueriesF fx) (run : Runs S I (ctxB X fx w H)) :
    S.Bound (ctxB X fx w H) (S.model1 (ctxB X fx w H)) (S.model2 (ctxB X fx w H)) ∧
      sp.Rest (ctxB X fx w H) (S.model1 (ctxB X fx w H)) (S.model2 (ctxB X fx w H)) ∧
      (hb.OutcomeRec (ctxB X fx w H) (S.model1 (ctxB X fx w H)) (S.model2 (ctxB X fx w H)) ∨
        X.ERec fx H)

theorem RSL.TASB.deployed_charge … (X : ExecB S R) (Ex : Expect X.Oracle) (fx : X.Fixed)
    (wOf : X.Oracle → X.World) (queries : X.QueriesF fx)
    (r m : X.Oracle → Rat) (T : Rat)
    (hm : ∀ H, 0 ≤ m H)
    (each : ∀ H, r H ≤ m H + ind (X.ERec fx H))
    (budget : Ex.E m + Ex.E (fun H => ind (X.ERec fx H)) ≤ T) :
    Ex.E (fun H => max (r H)
      (ind (Runs S I (ctxB X fx (wOf H) H) ∧
        ¬ hb.OutcomeRec (ctxB X fx (wOf H) H) (S.model1 (ctxB X fx (wOf H) H))
          (S.model2 (ctxB X fx (wOf H) H))))) ≤ T
```

The host averaging is the pointwise inclusion

```
∀ wOf H, max (r H) (ind (Runs … (ctxB X fx (wOf H) H) ∧ ¬ OutcomeRec …)) ≤ m H + ind (E_rec H)
```

proved from the stand-in lemma that the collision event is not charged twice and
from the inclusion of a failing run in the collision event.

The two host theorems, printed with `set_option pp.all true` and
`pp.proofs false` and quoted verbatim from the audit record
[`TAS_G0_AUDIT.json`](TAS_G0_AUDIT.json) (field `kernel_statements_verbatim`),
are these.

```
@AspisR1.TAS_FinalB.deployed_splitB : ∀ {W Tx : Type}
  (L0 : AspisR1.S2Trust.Library W (Nat → AspisR1.S2W_D189Entry.Record))
  (borrow : @AspisR1.S2Trust.S2TrustedSdkBorrow W (Nat → AspisR1.S2W_D189Entry.Record) L0)
  (copy :
    AspisR1.S2Trust.Heap (Nat → AspisR1.S2W_D189Entry.Record) →
      Nat → AspisR1.S2Trust.Payload → AspisR1.S2W_TrustedStd.Outcome (Nat → AspisR1.S2W_D189Entry.Record))
  (std : @AspisR1.S2W_TrustedStd.TrustedStd (Nat → AspisR1.S2W_D189Entry.Record) copy)
  (allocation217 : RSL.Bytes → RSL.Env → Bool) (allocation234 : RSL.TX2_234.Args → RSL.Env → Nat → Bool)
  (ch : NMX_R4_Authentication.Choices) (alloc2 : NMV_ConcreteWindows.Allocation) (fx : AspisR1.NOC_Run5bCtx.Fixed)
  (w : AspisR1.NOC_Run5bCtx.World W Tx) (H : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State)
  (queries :
    @RSL.TASB.ExecB.QueriesF (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std)
      (@AspisR1.NNH8_Exec.recSig W Tx L0 copy std) (@AspisR1.NNH8_Exec.exec W Tx L0 copy std) fx)
  (run :
    @RSL.TASB.Runs (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std) NNH_Libraries.L NNH_Libraries.V0 NNH_Libraries.VL
      (AspisR1.NNH_Run6Installed.implementation allocation217 allocation234 ch AspisR1.NNG_Candidate344.allocation
        alloc2)
      (@RSL.TASB.ctxB (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std) (@AspisR1.NNH8_Exec.recSig W Tx L0 copy std)
        (@AspisR1.NNH8_Exec.exec W Tx L0 copy std) fx w H)),
  have c : RSL.TAS.Sig.Ctx (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std) :=
    @RSL.TASB.ctxB (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std) (@AspisR1.NNH8_Exec.recSig W Tx L0 copy std)
      (@AspisR1.NNH8_Exec.exec W Tx L0 copy std) fx w H;
  And
    (RSL.TAS.Sig.Bound (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std) c
      (RSL.TAS.Sig.model1 (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std) c)
      (RSL.TAS.Sig.model2 (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std) c))
    (And
      (@AspisR1.NNH8_Split.rest W Tx L0 copy c (RSL.TAS.Sig.model1 (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std) c)
        (RSL.TAS.Sig.model2 (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std) c))
      (Or
        (@RSL.EVB.HeadlineB.OutcomeRec (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std)
          (@AspisR1.NNH8_Exec.recSig W Tx L0 copy std) (@AspisR1.NNH8_HeadlineB.headlineB W Tx L0 borrow copy std) c
          (RSL.TAS.Sig.model1 (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std) c)
          (RSL.TAS.Sig.model2 (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std) c))
        (@RSL.TASB.ExecB.ERec (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std)
          (@AspisR1.NNH8_Exec.recSig W Tx L0 copy std) (@AspisR1.NNH8_Exec.exec W Tx L0 copy std) fx H)))
```

```
@AspisR1.TAS_FinalB.deployed_charge : ∀ {W Tx : Type}
  (L0 : AspisR1.S2Trust.Library W (Nat → AspisR1.S2W_D189Entry.Record))
  (borrow : @AspisR1.S2Trust.S2TrustedSdkBorrow W (Nat → AspisR1.S2W_D189Entry.Record) L0)
  (copy :
    AspisR1.S2Trust.Heap (Nat → AspisR1.S2W_D189Entry.Record) →
      Nat → AspisR1.S2Trust.Payload → AspisR1.S2W_TrustedStd.Outcome (Nat → AspisR1.S2W_D189Entry.Record))
  (std : @AspisR1.S2W_TrustedStd.TrustedStd (Nat → AspisR1.S2W_D189Entry.Record) copy)
  (allocation217 : RSL.Bytes → RSL.Env → Bool) (allocation234 : RSL.TX2_234.Args → RSL.Env → Nat → Bool)
  (ch : NMX_R4_Authentication.Choices) (alloc2 : NMV_ConcreteWindows.Allocation) (fx : AspisR1.NOC_Run5bCtx.Fixed)
  (anchor : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State)
  (queries :
    @RSL.TASB.ExecB.QueriesF (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std)
      (@AspisR1.NNH8_Exec.recSig W Tx L0 copy std) (@AspisR1.NNH8_Exec.exec W Tx L0 copy std) fx)
  (wOf : (AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State) → AspisR1.NOC_Run5bCtx.World W Tx),
  And
    (∀ (H : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State),
      @LE.le.{0} Rat Rat.instLE
        (@Max.max.{0} Rat Rat.instSup (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
          (RSL.TASB.ind
            (And
              (@RSL.TASB.Runs (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std) NNH_Libraries.L NNH_Libraries.V0
                NNH_Libraries.VL
                (AspisR1.NNH_Run6Installed.implementation allocation217 allocation234 ch
                  AspisR1.NNG_Candidate344.allocation alloc2)
                (@RSL.TASB.ctxB (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std)
                  (@AspisR1.NNH8_Exec.recSig W Tx L0 copy std) (@AspisR1.NNH8_Exec.exec W Tx L0 copy std) fx (wOf H) H))
              (Not
                (@RSL.EVB.HeadlineB.OutcomeRec (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std)
                  (@AspisR1.NNH8_Exec.recSig W Tx L0 copy std)
                  (@AspisR1.NNH8_HeadlineB.headlineB W Tx L0 borrow copy std)
                  (@RSL.TASB.ctxB (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std)
                    (@AspisR1.NNH8_Exec.recSig W Tx L0 copy std) (@AspisR1.NNH8_Exec.exec W Tx L0 copy std) fx (wOf H)
                    H)
                  (RSL.TAS.Sig.model1 (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std)
                    (@RSL.TASB.ctxB (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std)
                      (@AspisR1.NNH8_Exec.recSig W Tx L0 copy std) (@AspisR1.NNH8_Exec.exec W Tx L0 copy std) fx (wOf H)
                      H))
                  (RSL.TAS.Sig.model2 (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std)
                    (@RSL.TASB.ctxB (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std)
                      (@AspisR1.NNH8_Exec.recSig W Tx L0 copy std) (@AspisR1.NNH8_Exec.exec W Tx L0 copy std) fx (wOf H)
                      H)))))))
        (RSL.TASB.ind
          (@AspisR1.BinRawByteCollisionTargets.event
            (AspisV8R19.MemoizedProgramLaw.View AspisV8R19.DuplexFrames.Bytes AspisV8R19.SourceDuplexStep.State
              (AspisR1.GExq_AccountExperiment.Outcome Bool))
            (@FS2.Duplex.Params.iv AspisR1.SelectedTranscriptParams.Message AspisWideTower.WideExact
              AspisR1.SelectedTranscriptParams.L AspisR1.SelectedTranscriptParams.params)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (AspisR1.NNH_HostCtx.Fixed.Q0 fx)
                (AspisR1.NNH_HostCtx.Fixed.Q1 fx))
              (@OfNat.ofNat.{0} Nat (nat_lit 2965) (instOfNatNat (nat_lit 2965))))
            (@AspisV8R19.MemoizedProgramLaw.eval AspisV8R19.DuplexFrames.Bytes AspisV8R19.SourceDuplexStep.State
              (AspisV8R19.MemoizedProgramLaw.View AspisV8R19.DuplexFrames.Bytes AspisV8R19.SourceDuplexStep.State
                (AspisR1.GExq_AccountExperiment.Outcome Bool))
              H (AspisR1.NNH8_RecorderFixed.fixedProgram copy fx anchor)))))
    (And
      (@LE.le.{0} Rat Rat.instLE
        (@AspisV8R19.MemoizedProgramLaw.lazyMean AspisV8R19.DuplexFrames.Bytes AspisV8R19.SourceDuplexStep.State
          (AspisV8R19.MemoizedProgramLaw.View AspisV8R19.DuplexFrames.Bytes AspisV8R19.SourceDuplexStep.State
            (AspisR1.GExq_AccountExperiment.Outcome Bool))
          (@Pi.instFintype.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))
            (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))) =>
              AspisV8R19.DuplexFrames.Byte)
            (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))
            (SimplexCategory.instFintypeToTypeOrderHomFinHAddNatLenOfNat
              (SimplexCategory.mk (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))))
            fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))) =>
            SimplexCategory.instFintypeToTypeOrderHomFinHAddNatLenOfNat
              (SimplexCategory.mk (@OfNat.ofNat.{0} Nat (nat_lit 255) (instOfNatNat (nat_lit 255)))))
          (fun (a b : AspisV8R19.DuplexFrames.Bytes) =>
            @instDecidableEqList.{0} AspisV8R19.DuplexFrames.Byte
              (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 256) (instOfNatNat (nat_lit 256)))) a b)
          (AspisR1.NNH8_RecorderFixed.fixedProgram copy fx anchor)
          (@FS.emptyTable AspisV8R19.DuplexFrames.Bytes AspisV8R19.SourceDuplexStep.State)
          fun
            (v :
              AspisV8R19.MemoizedProgramLaw.View AspisV8R19.DuplexFrames.Bytes AspisV8R19.SourceDuplexStep.State
                (AspisV8R19.MemoizedProgramLaw.View AspisV8R19.DuplexFrames.Bytes AspisV8R19.SourceDuplexStep.State
                  (AspisR1.GExq_AccountExperiment.Outcome Bool))) =>
          AspisV8R19.CausalFirstHitUnionBound.indicator
            (@AspisR1.BinRawByteCollisionTargets.event
              (AspisV8R19.MemoizedProgramLaw.View AspisV8R19.DuplexFrames.Bytes AspisV8R19.SourceDuplexStep.State
                (AspisR1.GExq_AccountExperiment.Outcome Bool))
              (@FS2.Duplex.Params.iv AspisR1.SelectedTranscriptParams.Message AspisWideTower.WideExact
                AspisR1.SelectedTranscriptParams.L AspisR1.SelectedTranscriptParams.params)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (AspisR1.NNH_HostCtx.Fixed.Q0 fx)
                  (AspisR1.NNH_HostCtx.Fixed.Q1 fx))
                (@OfNat.ofNat.{0} Nat (nat_lit 2965) (instOfNatNat (nat_lit 2965))))
              v))
        (AspisR1.F3T_Numeric.total
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (AspisR1.NNH_HostCtx.Fixed.Q0 fx)
            (AspisR1.NNH_HostCtx.Fixed.Q1 fx))))
      (∀ (H : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State),
        have c : RSL.TAS.Sig.Ctx (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std) :=
          @RSL.TASB.ctxB (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std) (@AspisR1.NNH8_Exec.recSig W Tx L0 copy std)
            (@AspisR1.NNH8_Exec.exec W Tx L0 copy std) fx (wOf H) H;
        @LE.le.{0} Rat Rat.instLE
          (AspisR1.F3T_RuntimeBound.failureModel
            (@AspisR1.NOC_Run5bHost.runtime W Tx L0 copy c
              (RSL.TAS.Sig.model1 (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std) c)
              (RSL.TAS.Sig.model2 (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std) c)))
          (AspisR1.F3T_Numeric.total
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (AspisR1.NNH_HostCtx.Fixed.Q0 fx)
              (AspisR1.NNH_HostCtx.Fixed.Q1 fx)))))
```

## Appendix B. Interface fields

Every interface field is a delivered closed term at the seventh assembly run.

| Field | Delivered as |
| --- | --- |
| nmn | Dropped by ruling (bu)(2) |
| nms, g1a | Their (bu) forms, `NNT_Field.r241` and `NNT_G1aLaw.field` |
| nmfB | `NNH8_NMF.nmfB` |
| hb | `NNH8_HeadlineB.headlineB` |
| sp | `NNH8_TopHost.split` (`NNH8_Rest.assemble`) |
| a0, r0 | From `NOC_Run5bHost` |
| a1 | `AspisR1.NOQ_FinalCombined.field` |
| a2 | `AspisR1.NOF_A2FieldCorrected.field` |
| a3, a4, a5 | `NNH8_Acceptance` |
| X, R, rs | In `NNH8_Exec` |

## Appendix C. Instantiated binders

| Binder of the headline | Instantiated as | Why it is not a restriction |
| --- | --- | --- |
| `native1`, `native2` | The owned stage models | The actual code meets the models through the actual-code rows and the a1 and a2 fields; extraction at native := model then holds by `rfl`, except the digest source, which ruling (bt) supplies |
| `A`, `allocator`, the four states | `Bool`, the abort indicator, all `true` | A run that returned successfully had every allocation succeed, since a failed allocation aborts the program |
| `CoreError` | The error type of the extracted frozen core library | The installed configuration is the deployed one, so this names the type the deployed code uses; the value `fx.indexError` stays universal |
| `a`, in the pair and in `queries` | `a⊤`, the normalised adversary | Allocator state models allocation success, which the deployed attacker does not control; `a` itself stays universal |
| The pair `e1 data1 state1`, `e2 data2 slot state2` | The outputs of `a⊤` at H in each phase | Realisation holds by construction at every H; instantiating `a` to a constant adversary is forbidden |
| `hashv`, `sha256`, `p1`, `syscall` | The hash adapter at H, H, `rfl`, and the host syscall theorem | The adapter is the only total hash the syscall assumption admits, and every consumed run returned, so the model agrees with the runtime on every consumed run |
| `missing` | The corrected host seed, selected for the second transaction's configuration | A substitution of a universal binder. The seed installs the zero-filled allocation as the frozen source writes it, under the existing allocator assumption; the old seed left it as a placeholder that never returned, so the old host never accepted a first transaction. Lean proves by `rfl` that only that operation and one SDK slot changed. No contract or trust change. The program-address derivation and clock now quantified in the fixed data are universal, so they restrict nothing |
| `extraction`, `accepted1`, `accepted2`, `game` | Derived, no longer binders | Derived from the row roots, the a0 to a5 fields and the description of the run |
| `alloc1`, the first stage's allocation stream | `AspisR1.NNG_Candidate344.allocation` | Statement data fixed by the ledger's final entry, never a hypothesis; the other allocation streams stay universal |
| `admission1`, `admission2`, `RuntimePersistence` | Conjuncts of the run's frame | No longer separate binders; the same trust assumptions, stated as facts of the actual run's world |

## Appendix D. Retained binders and hypotheses

| Binder or hypothesis | Kind | Notes |
| --- | --- | --- |
| `{W Tx}` | Universal types | The library world type and the transaction index type, unconstrained |
| `L0` | Universal data | The abstract SDK library, constrained only through `borrow` |
| `borrow` | Trust (`S2TrustedSdkBorrow`) | The headline's `sdk`; all 15 fields assumed |
| `copy` | Universal data | The slice copy, constrained only by `std` |
| `std` | Trust (`TrustedStd`) | The W1 qualification retained |
| `allocation217`, `allocation234`, `ch`, `alloc2` | Universal data | Allocation success streams for the second stage's windows and rows, and the account-authentication choices; there is no allocator-success trust item |
| `fx`, twelve fields | Universal | Address derivation, clock reply, reservation, index error, root, length, prior program, transcript words, decoder, the adversary `fx.a` (arbitrary and adaptive, never constant), and the budgets `Q0`, `Q1`. The model and recorder are proved independent of the clock; the physical clock reading is the clock assumption |
| `w` (first theorem), `wOf` (second) | Universal | Two runtime worlds, saved checkpoint, heaps after each stage, transaction lineage and actions; may depend on H arbitrarily through `wOf` |
| `H` (first theorem), `anchor` (second) | Universal | `anchor` is fixed program data, not a condition on the sampled oracle |
| `queries` | Statement parameter | The Q of the bound, not discharged. It requires the issued-call bound on `a⊤` to hold for every pair of an environment digest and a query oracle |
| The run's frame (first theorem only) | The approved game together with the two admissions and persistence | A statement of the approved experiment, not an attacker restriction; its unfolding is exact by `Iff.rfl` |
| The run's trace (first theorem only) | The physical trace association | Every invoke action was executed as the entry at the recorded images, and every action that is not the verifier's is the recorded pool or runtime action; this is where the pool enters |
| The run's success and outputs (first theorem only) | The attack's success antecedent | Both entries returned successfully with their recorded outputs |
| `admission1`, `admission2` | Trust (`RuntimeEntrypointAdmission`) | Inside the run's frame |
| `RuntimePersistence` | Trust | Inside the run's frame |
| Account counts, 3 and 7 | Host facts | Not hypotheses |

## Appendix E. Terms of the bound

| Term | Meaning | Source of the constant |
| --- | --- | --- |
| (Q+34)·B | Start charge: every fresh transcript start, among the adversary's Q queries and the 34 starts the submitted transcript reads in the prover and sampler prefix before terminal authentication, succeeds with probability at most B | The start-charge analysis, with Q + 34 starts |
| collisionLoss(Q) | Collision mass over at most Q + 1,161 distinct first reads, 1,161 being the verifier envelope | The frozen bound |
| accountLoss(Q) | The collision event of the adversary's capped run: at most Q + 1,921 first reads plus 1,044 audit reads, Q + 2,965 in all. Charged once inside the failure probability in compiled Lean; for the per-attempt event including the outcome statement the single charge rests on a stand-in lemma | The binding-or-collision and mass lemmas |
| 2^-126 | Extractor abort allowance: accepted, no hit, extractor still returns nothing | Lean, and the contract table of 21 October 2026 |
| 2^-454 | Query-scan exhaustion | Lean, and the contract table of 21 October 2026 |

## Appendix F. The reconciled trust inventory

### Oracle and cryptographic model

| Assumption | Exact statement | How it enters | Removal condition | Confirmed |
| --- | --- | --- | --- | --- |
| Random-oracle model for SHA-256 | SHA-256 as invoked through the runtime hash syscall is a uniformly random function H; every probability is over H | The failure probability, the lazy mean, the collision event and the second theorem | None; a standard-model argument would be a different theorem | Contract, 26 October 2026 |
| P1, ideal-oracle realisation | For all bytes, sha256 bytes = H bytes, at the supplied world | Instantiated with sha256 := H; justifies reading the physical hash replies of a run as values of H | None; inherent to the random-oracle reading | Appendix, 27 October 2026 |
| `RuntimeSyscall` | A returning hash call decodes to the SHA-256 of the flattened parts; no totality | Instantiated by a host theorem; the physical reading of every returned digest | Proposed: a proof that the pinned runtime's `sol_sha256` returns the SHA-256 of exactly the passed slices | Contract, 26 October 2026 |
| `RuntimeSha256Value` | The SDK hash reply value realises H; exact request slices and an unchanged reply are separate bridge obligations | Reached because every accepted run reads hash replies as H, although its listed ledger consumers' roots are outside the cones | Proposed: none for the value part; for realisation, a proof that the pinned `sol_sha256` returns the SHA-256 of the exact slices, which would reduce this to P1 | Ledger, accepted retained trust, 21 October 2026 |

### Solana runtime behaviour

| Assumption | Exact statement | How it enters | Removal condition | Confirmed |
| --- | --- | --- | --- | --- |
| `RuntimeEntrypointAdmission` (verifier) | At each of the two verifier entries (3 and 7 accounts): initial heap validity, fresh guards, zero counters and external borrows, live accounts, key and cell alias consistency | Part of the run's frame; the whole structure is assumed, though only three fields are used inside the cones | Proposed: a proof of the pinned BPF loader's input serialisation together with `solana_program::entrypoint::deserialize` at 2.3.0. Narrowing the hypothesis to the fields used would change the statement and need a before-and-after audit | Contract, 26 October 2026 |
| `RuntimePersistence` | For consecutive transactions on one lineage, an ordinary account's loaded data bytes are the previous transaction's tentative bytes if it succeeded and its starting bytes otherwise; data bytes only, zero lamports meaning absent. Signing accounts and accounts owned by the System program are excluded, a restriction of the approved domain | Part of the run's frame; the historical checkpoint binding is constructed from it | Proposed: a proof of the deployed validator's account commit and load between consecutive transactions; none is available for Agave | My amendment, 26 October 2026 |
| `Allocator` | Allocate and clean-up with no success proposition | Instantiated at the abort indicator, states true; the physical reading that a failed allocation aborts is proposal D.5 below | Not applicable as a free binder | Contract, 26 October 2026 |
| `RuntimeClockSlotBinding` | A successful clock read returns the bank slot, within one instruction; nothing about success, monotonicity or epochs | A window law of the second stage; the model and recorder are clock-independent | A proof of the pinned clock sysvar | Added 5 November 2026; provisional, still to be confirmed |
| `RuntimeReturnDataClear` | Empty return data leaves nothing observable until a later set, within one instruction | A window law of the second stage | A proof of the pinned return-data register | Added 6 November 2026; provisional, still to be confirmed |
| `RuntimeReturnData` | For length 1 to 1,024, setting return data and immediately reading it in the same instruction with no intervening call returns it with the program id | The verifier's result emission; the pool-side readback association is open and outside the theorem | Proposed: a proof of the pinned return-data register | Accepted by me, 4 November 2026 |
| `RuntimeMemcmp` | For the same two valid readable 688-byte ranges, a normal return, zero exactly when the bytes are equal, no other effect | The proof-buffer scan on the deployed path | A trust-reduction study of the pinned `sol_memcmp_`, recorded but not commissioned | Accepted by me, 4 November 2026 |

### Library and SDK

| Assumption | Exact statement | How it enters | Removal condition | Confirmed |
| --- | --- | --- | --- | --- |
| `S2TrustedSdkBorrow` (15 fields, `solana-account-info` 2.3.0) | Data-borrow and `RefCell` guard semantics; no caller result | The binder `borrow` in both theorems; all 15 fields assumed, two used inside the cones | Proposed: a Lean proof of the fifteen fields against a translation of the pinned borrow functions and `RefCell` guards, once a translator handles guard drop; today there is no tool route | Appendix, 27 October 2026 |
| `TrustedStd`, slice copy (W1) | Pinned `copy_from_slice` on valid borrowed references: equal lengths copy into the destination only, unequal lengths panic; each use needs justified validity | The binder `std` in both theorems | Proposed: a Lean equality between the copy on its valid domain and the pinned Aeneas model of `copy_from_slice`, with the validity fact at each use; a proof task | Appendix, 27 October 2026 |
| `TrustedStd`, Option and Result | Pure Option and Result interpretations | Not reached as a hypothesis; the cones use concrete models whose library reading is the Option and Result combinator assumption below | Kept | Appendix, 27 October 2026 |
| `SdkTypeModels` | The Lean types and functions for the SDK's `Pubkey`, `Hash`, `PubkeyError` and `ProgramError` faithfully model the pinned crates; also the deployment id constant (the address macro applied to the source literal, shown equal to the id slot of both rebuilt ELFs) and the upgradeable loader id | Reached; 42 closed statements | The SDK items given as translated and compared definitions, or each consumer shown to use only the byte content | Accepted 10 November 2026; the deployment id by my decision |
| `CoreSliceIteratorModel` | The Lean models of the core slice and array iterators behave as the pinned Rust core library on the arguments reached | Reached; 145 closed statements | Aeneas library definitions proved against a Lean specification, or re-translation with index-based loops | Accepted 10 November 2026 |
| `CrossCrateConstantEncoding` | An Aeneas external standing for a cross-crate constant denotes that constant's value | The provenance records conditional on such bindings | Removed constant by constant as each is proved equal | Accepted 10 November 2026 |
| `CoreOptionResultCombinators` | The Lean definitions of `Option::ok_or`, `Result::map`, `Result::map_err`, the `?` instances, Option equality and the reservation error type are the Rust semantics at the translation toolchain; also `Vec::try_reserve_exact`, read as succeeding with enough capacity or failing with the vector unchanged. No differential check | Reached; 205 closed statements | The Aeneas library definitions with one generic equality lemma per combinator | Entered 10 November 2026 under my trust-boundary decision |
| `CoreArraySliceOps` | The Lean definitions of `Array::map`, slice and array equality, windows, `first` and full-range indexing are the Rust semantics at that toolchain; also `core::array::from_fn`, on condition that the hand model is proved in one lemma to give f(i) at index i in index order, until which its 66 or so consumers stay open. No differential check | Reached; 128 closed statements | Aeneas library definitions with a generic lemma per operation, or re-translation without the operation | Entered 10 November 2026 |
| `CoreNumOpsIterModels` | The Lean definitions of `u16` `count_ones` and `trailing_zeros`, range clone, reverse and inclusive-range folds and the default `all`/`any` are the Rust semantics at that toolchain. A differential check of the two bit functions on all 65,536 inputs agreed, run with a different compiler, so only a plausibility check | Reached | Proofs against the Lean integer library, or re-translation | Entered 10 November 2026 |
| `AeneasDiscriminantHelpers` | Aeneas's discriminant registration and reading are accepted as tool post-processing; reading discriminants of Aspis's own enums stays a proof item | Reached | The Aeneas-native form, or a proof that the registration's reading equals the match-based discriminant | Entered 10 November 2026, narrowed by the lead |

### Translation, tools and realisation

| Assumption | Exact statement | How it enters | Removal condition | Confirmed |
| --- | --- | --- | --- | --- |
| `AeneasExtraction` (D188), trace fidelity | The pinned Charon and Aeneas translation of each associated frozen body preserves the accepted result and the chronological attempted hash-call sequence, rejected prefixes both rejecting. Bodies failing the dropped-write scan or native differential get no credit and are bridged natively; the translation is faithful except for explicit returns or `?` in post-loop code merged into a loop exit, so each body relied on must be free of that pattern or have the affected exits certified natively | Instantiated at the top, and tool trust for every translated body in the cones | None for the tool; for release, every reached translation receipted or proved equal to a fresh one | Approved by me, 27 October 2026 |
| P6, Kani association | Pinned Kani as evidence for checked associations between a frozen body and its reference; credit only without copy built-ins, or with the recorded element-wise copy stubs and a matched failing control; timeouts earn nothing | Tool trust for the native halves of every hybrid statement | None for the tool | Appendix and fourth amendment |
| `NativeContractSemanticTransport` | Kani's and Aeneas's readings of the enumerated frozen bodies and references denote the same Rust semantics, with the recorded association of the entries and digest wrapper to their Lean parameters | 380 closed statements, 84 with a root in the cones | Proposed: none for the tool; per use, replacing the Kani and Aeneas pair by a translated body of the frozen function proved equal to the reference | Approved by me, 28 October 2026 |
| P7, compiler and pinned libraries | The selected compiler, toolchain and ABI and the pinned Lean, Mathlib and Aeneas base, for the exact recorded source, features and toolchain | Tool trust for the whole closure | None for the tool | Appendix, 27 October 2026 |
| `AllocatorABICompilerSourceToELF` | The binding to the concrete final artefact | The composed rows and the physical reading of allocation abort | Discharged only by the final audit; the reproduction half is met, the rest is split into proposals D.1 to D.7 | A ledger obligation, not an approved trust assumption |
| Standard logical axioms | `propext`, `Classical.choice`, `Quot.sound` only | Walked and collected sets equal for all four roots on the replayed objects | None. The replayed closure holds 105 nonstandard axiom declarations, the same set as on 27 October 2026, none reachable from any root; a strict import-wide check still fails | Appendix, 27 October 2026 |
| `CheckedVsWrapping` (R22) | The translations are checked while the deployed ELFs wrap; the theorem is about checked semantics, and transfer to the binary needs every reached path total or wrapping acceptance to imply checked acceptance with the same result. Of 197 executed checked definitions, 73 are total, 52 have one bounded increment or checked read, 72 have their precondition proved from callers, and none is open; none of the 393 closed statements they serve depends on an open definition. Seven textual reliances remain as named review items, each to become a Lean statement or an item accepted by name. No reachable input is known on which the wrapping binary accepts and the checked model rejects | Every closed statement on the translated-body route, through the source-to-ELF association | The totality audit closing on the final closure, or its being recorded as retained trust | Not yet decided by me |

### Constructed, not assumed

The historical checkpoint interfaces are reached as constructed terms built from
the persistence assumption, the game and source proofs, and are never a
hypothesis.

### Reviewed transcriptions

Under the rule adopted on 10 November 2026 the transcriptions of Aspis code are
to be discharged by a translation proved equal, the statements using them being
conditional until then, and the rule covers the transcriptions accepted on
27 October 2026 as well.

| Item | Function | Reached | Removal condition |
| --- | --- | --- | --- |
| TX1:344 | `stage1` | Yes | A native certificate on the frozen `stage1` |
| TX2:240 | `stage2` | Yes | A native certificate on the frozen `stage2` |
| TX2:217 | `decode_lane_from_pool_release` | Yes | A native certificate on the frozen function, paired with the same translated reference and with no transcription reliance |
| prepared_claim | `prepared_claim` | Yes | A translated body proved equal to the transcription |
| polynomial | `verifier.rs::polynomial` | Yes | Proposed: a translated body proved equal to the reverse-fold transcription |
| queries_from_pairs | `queries_from_pairs` | Only through a shared root; kept as reached | A translated body proved equal to the transcription |
| batch_tree | `batch_merkle`, `batch_merkle_values`, `batch_tree` | For the second-transaction rows only | A translated body passing the post-loop-exit check, proved equal to the transcription on the same arrays and histories, or a native certificate without the transcription |
| NJY-RT149, 152, 153, 201, 203 | Pool identity, checkpoint and master decoders; registry entry and registry decoders | Yes, through the installed decoder slots | A translated body proved equal to the hand reference |
| NJZ-RT189 | `echeck` | Yes | A translated body proved equal to the transcription, or a native certificate without the reviewed patch |
| NJZ-RT201 to 204 | `pool_v1_tree_parent`, `IncrementalMerkleTreeV1::default` and `::empty`, `pool_v1_empty_roots` | No | As NJZ-RT189 |
| NKJ-RT036, 040, 041, 043, 044 | The QM31 accumulate and sum-of-products functions | No | A translated body proved equal to the transcription, or one native certificate on the whole frozen function without cuts or fission |
| NKM-RTNGB002, 004, 006 | The circle fallback and secure circle-point functions | Yes | As NKJ |
| NKI-RT234, 260, 233 | `append_level_packed_selector_tensor`, `semantic_initial_and_absorption`, `add_value_lanes` | Yes | As NKJ |
| NKL-RT084 | `canonical_scan` | Yes | As NKJ |
| NKU-RT124 | `resume` | Yes | As NKJ |
| NKY-RT235, 216, 218 | `append_levels_packed_selector_tensor`, `decode_checkpoint_box`, `decode_master_box` | Yes | As NKJ |
| NKR-RT-232, 218 | `add_schedule_lanes`, `evaluate_with_selectors` | Yes | As NKJ |
| NKR-RT-225, 251, 250, 220 | `qm31_sum_products_up_to4`, the two public-digest functions, `finish_selector_tensor_basis` | No; for the public-digest pair the certificate explicitly does not equate its reference with the model the cone uses, which takes its link to the frozen code from translation and provenance | As NKJ |
| NLH-RT-261, 237, 263, 256 | `semantic_packed`, `composition_parts`, `terminal_parts`, `terminal_qm31` | Yes | As NKJ |
| FieldDerives | The derived `Clone` and `PartialEq` on M31, CM31, QM31 and WideExact | Kept after re-examination under the rule above, since these are compiler derive expansions | A translation of the derived impls with a proved equality to the transcription |

Of the 37 inventory entries, 24 are reached and 13 are not. A transcription of
the public-preparation accessor `public_bytes` was withdrawn under my
rule, because it is Aspis code; its per-loop equalities remain as evidence, the
newer tool now translates the function, and it is proved equal to its fresh
translation with no assumption named.

### Kept and marked unreached

| Assumption | Why unreached | Would enter if |
| --- | --- | --- |
| `RuntimeCpiAccountView` | No pool call in either cone | The pool's execution is brought into the game |
| `RuntimeEntrypointAdmission-Pool` | Pool entry point only | The same |
| Six pool reviewed transcriptions | Pool statements only, none on the verifier | The same |
| `RuntimeCpiReadonlyEntry7` | Pending, never admitted, unused | An admission decision |
| `FixturePdaRuntime` | No constant of it in either cone; the address derivation is quantified in the theorem | The non-vacuity witness is built on the fixture |
| The semantic-transport reclassification for TX2:064 | Its root left the top | The top reinstates that field |

If the pool decision chooses the conditional boundary, the claim's first
sentence must mention the pool assumptions.

### Proposed and not adopted

These are proposals awaiting classification as trust, proof task or
discharged; none is a trust assumption today.

| Proposal | Statement |
| --- | --- |
| Shift-amount bridge | Verified in Lean and recommended for recording as a bridge, not trust, with the restriction that it is never reused for checked shifts with amounts wider than 32 bits; residuals are an SBF-target build check and the shared Lean `usize` width |
| R22 decision | Whether the overflow obligation is retained as trust if the totality audit does not close |
| D.1 compiler | Platform-tools v1.52 rustc preserves the semantics of the frozen source under the deployed profile |
| D.2 LLVM and LLD | The pinned LLVM, clang and LLD preserve the IR semantics |
| D.3 `cargo-build-sbf` | Selects the recorded flags and strips the ELF (reproduced bit for bit, not proved) |
| D.4 registry crates | The registry sources are those the `Cargo.lock` checksums name; removable with an archived snapshot or a vendored build |
| D.5 allocator ABI | The runtime maps a heap region of at least the requested size, and any out-of-region access or allocation failure ends the instruction with an error and no committed state |
| D.6 loader and VM | The deployed loader loads the ELF as recorded, resolves its imports to the documented syscalls and executes SBF semantics, including the 4 KiB frame limit |
| D.7 stack frames | The 34 functions with stack-offset diagnostics are absent from the linked ELF (a name-level check, not a frame-size proof) |
| Others | Allocation models, frozen-crate item models and gate-side adaptations, other hand models, the `from_fn` bridge (superseded by the condition above) and parametric records including the operation dictionary, which is reached. Up to 99 external declarations are unresolved by any row; of these the library ones join the library assumptions and 68 Aspis entries remain open Aspis-side obligations |

The proof work that stays on the Aspis side is the `from_fn` lemma, the
parametric records and offset constants, the equalities between fresh and
committed translations, the definitions that exist only in the committed Lean,
and the overflow obligation.

### Two second-stage functions the translator cannot handle

Neither tool version translates `decode_lane_from_pool_release` (because of
early returns inside loops) or the deployment-id constant. A reviewed
transcription was not accepted for the decoder, so it stays an open source-refinement
obligation whose closing route is tool work; the proved equality between the
deployed decoder slot and a transcription is kept as evidence only. The
deployment-id constant was accepted as a member of the SDK type-model
assumption, on the strength of a byte receipt comparing the Lean literal with
the id slot of both rebuilt ELFs, so its slot depends on library trust and is
not open. Five further second-stage adapter slots and three related operations
are proved equal to fresh translations, each conditional on decoders and
encoders that are not yet translated; one of them logs on its frozen error path
where the model does not, which is a privacy observable and irrelevant to
soundness; and several other slots still have no translation or equality.

### Stale ledger records

Four consumer records in the ledger are stale and noted without changing any
row: persistence lists no consumers though it is used at the top; the
return-data clear record says it is unused though the second stage uses it; some
runtime assumptions are reached through the deployed path even though their
listed consumers' roots are outside the cones; and two rows record no root.

## Appendix G. Release items

| Item | Requirement | Status |
| --- | --- | --- |
| 1. Rows | A ledger with 599 closed, 0 qualified and 0 open, from an all-slices composition check with a standard-only axiom walk and a clean reference scan | Met |
| 2. Top fields | Every interface field a delivered closed term of exactly its type | Met |
| 3. Host theorems | Both compiled in the combined import with only standard axioms, no `sorry`, and full records | Met (48.8 s, peak 6,881,368 KiB, no swap) |
| 4. Statement audit | Printed statements quoted verbatim, with the written confirmations of section 1.4 | Met |
| 5. Non-vacuity | A world and the run facts built from a recorded trace, showing the game and trace predicates are the physical facts | Partial. From the recorded transfer, Lean proves the frame, game, trace association, outputs, admissions, persistence, query bound and retained trust facts are the recorded facts; what remains is the trace, the first transaction's acceptance and output and the second's acceptance. Executable evidence: both transactions accepted by the model in Lean's interpreter on the recorded bytes, and the first transaction's reference value equal to the recorded checkpoint; this is not a proof. The second transaction's reference value could not be evaluated within the resource limits and is not established. Kernel-level execution of the entry point is blocked by two model sites, and how to treat them is undecided; the likely course is for the item to rest on the executable evidence and the proved first-stage equivalence, with a restatement only if a reviewer requires a kernel-level witness |
| 6. Averaging obligations | The recorder at the hash adapter equals the recorder at a fixed returning hash, and is independent of the environment's hash | Met by the seventh assembly run, which proved the condition with every field delivered; no separate artefact |
| 7. Provenance | Every reached translation reproduced or proved equal | Open; see section 7 |
| 8. Cold replay | The final closure rebuilt from committed sources under capped scopes | Met |
| 9. Final audit | Trust and axiom audit, and the source-to-ELF association | Reproduction of both ELFs met; axiom audit met; trust audit done but not met; the overflow review items, the realisation proposals, the per-class provenance closure and the pool remain |
| 10. Trust inventory | One to one with the closure, with removal conditions and confirmation status | Not met until the provisional runtime assumptions and transcriptions are confirmed or rejected and each proposal is classified |
| 11. Pool boundary | The choice recorded, then a proof or a named condition | Open |
| 12. Panic path | Exclusion or reachability recorded, or the liveness caveat stated | Open |
| 13. Campaign accounting | The reduction reviewed or proved, or per-attempt wording | Open |
| 14. Frozen pins | The source at `4bb3b3f` and the pool at `b936275`, with any change assessed | The pins are as stated |
| 15. Toolchain consistency | One pinned Lean toolchain for the final host build and the stand-ins | Met by the cold replay, which rebuilt all 14,101 modules, the stand-ins included, on one toolchain (Lean v4.32.0) |
| 16. Overflow semantics | Every reached path total or with its precondition proved, or retained trust named in the claim | All 197 definitions settled; seven review items remain |

## Appendix H. Findings

| No. | Finding | Status |
| --- | --- | --- |
| 1 | Closing the ledger rows did not by itself assemble the top; the top obligations had to be delivered | Closed at the seventh assembly run |
| 2 | The stand-in's documentation placed the admissions, the hash binders and the environment among the oracle-free binders, though they depend on the adversary's outputs; they belong in the per-world block, which keeps the quantifier strength | The host build must make the move; the stand-in documentation is wrong as written |
| 3 | Q is counted on `a⊤`, which can issue more verifier calls than `a` | Wording point; no soundness problem seen |
| 4 | The environment instance named in the stand-in was never delivered; the intended instance is the literal one | The literal instance is to be built |
| 5 | How the extracted witness is tied to the spend relation was not re-audited for this draft | The final statement audit must confirm it |
| 6 | Campaign accounting | Stand-in compiled; host obligations open; the choice of units undecided |
| 7 | The pool enters through the trace hypothesis | Until the decision, the wording is "conditional on the recorded Pool and runtime actions in the lineage" |
| 8 | A ledger finding was listed open against two rows recorded as closed | Resolved |
| 9 | The first-transaction preparation caveat at five retired interfaces; later native bridges and a transcription replaced much of that route | The final audit must confirm each of the five is covered |
| 10 | Missing removal conditions for several assumptions and the 36 transcriptions | Addressed in the reconciled inventory |
| 11 | Checked versus wrapping arithmetic was absent from earlier drafts | Now tracked as the overflow obligation |
| 12 | The inclusion lemma at the host is a restatement of the stand-in's over the current interface; non-vacuity was only definitional; the second theorem gives two separate facts and no single program mean | It has still to be confirmed that the restatement satisfies the section 1 wording; non-vacuity now partial with executable evidence |
| 13, 14 and 14a to 14m | The provenance campaign, its counts, corrections and tool trials | Counts at research `9fb1e206d7d`, 10 November 2026, from the counting script: 1,150 settled, 428 not settled, 129 other of 1,707; 122 of 599 statements settled-only |
| 15 | Cached-closure coherence | The theorems are credited on the replayed closure |
| 16 | 599 closed statements are not 599 dependencies | The published claim must not present the count as the dependency size |
| 17 | Reviewed transcriptions outside the cones were checked one by one | Settled: 15 feed an installed model and are reached, 13 feed nothing |
| 18 | One Rust model for soundness and privacy; the proving client is not built from the pin | Pin description undecided |
| 19 | The host re-instantiated at the deployed addresses | Delivered; the 10 November 2026 instance is the release instance |

## Where this comes from

This page is written from the status document on the
[`research`](https://github.com/DJBarker87/aspisZK/tree/research) branch,
`docs/research/100bit-spend-path-20261013/design/SOUNDNESS-CLAIM-DRAFT-20261108.md`,
at commit `90795727483`. The Lean statements in Appendix A are copied verbatim
from it, and through it from the audit record of the final assembly. The
evidence directories, job receipts and rulings it cites are on that branch.
