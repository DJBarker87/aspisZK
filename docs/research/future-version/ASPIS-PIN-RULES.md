# Aspis: rules for the pin and for the translation that precedes it

Status: target not yet established. This note records rules and decisions. Nothing in it is a
proof, and no translated function is a verified function.

Date: 12 November 2026. It supersedes section 10 of ASPIS-FREEZE.md where the two differ: the
commit frozen that morning (3d700effcab) is not the final pin.

## 1. The owner's directions of 12 November

In the owner's words, in order:

- "make sure everything required is extracted and then start the proof worlk", then "that should
  be for both soundness and privacy. Only once everything is extracted are we truly ready to
  proceed".
- "ok i just want to make sure we dont run into the same provenance bulshit as before. also i
  would rather rewrite the rust now than later".
- To the soundness lead, as relayed by it: "i would much rather move the pin a number of times
  now that after proof work has started", and "rewrites are fine but they cant bloat to the point
  cu rockets".
- On compiling the generated Lean against the translator's own library: "yes recompile". The
  cost was first described to the owner as a recompile; it is a port (section 7), and the owner
  was told so.
- On writes to account data, after the options of section 5 were put: "agree with
  recommendastion". Read by the lead as acceptance of the named class of section 5, and said so
  to the owner.
- Crate names stay as frozen ("A"); the lead's calls of the freeze night stand.

Consequences. No proof work on Aspis starts until one commit has a clean translation of the
verifier program, the Pool program and the prover. Code the tools reject is rewritten, in gated
rounds on the candidate branch `aspis-next`. The pin is declared only on such a commit, and does
not move once proof work has started. Devnet is redeployed once, at that pin.

## 2. Rules agreed with the soundness lead

These are the lead's and the soundness lead's implementation of the owner's wish that the
provenance campaign of the two-transaction proof is not repeated. They are not the owner's words.

1. One commit for the verifier program, the Pool and the prover, for soundness and privacy. The
   pin is declared at the deployed configuration (the resolved `aspis` feature set, overflow
   checks off; for the prover the client configuration `r1p-check` alone). No emission of a
   candidate or rewritten crate is ever a proof base. An emission at another overflow setting is
   a diagnostic only.
2. One scripted emission per program from that commit, raw output recorded by hash, never edited
   by hand. "Clean" means all of section 3.
3. Every Aspis theorem is stated about definitions of those emissions. No theorem about a copy, a
   transcription, a hand model or a definition emitted for the two-transaction proof is credited.
   Every bodiless declaration is a definition of the translator's library at the pinned commit,
   or a named standard-library, SDK or runtime trust row. No hand-written model file for a
   library item. An Aspis item in a list of bodiless declarations blocks the pin, with the single
   class of section 5.
4. A result of the two-transaction proof is reused only through a compiled Lean equality with
   the emitted definition; otherwise it is proved again. No row is credited on a text-identity
   receipt. The soundness lead's estimate is that few of the 279 unchanged functions will be
   definitional, so this reuse is a bonus and not the plan.
5. A mechanical check at the top: the dependency closure of the top theorem contains, for Aspis
   code, only modules of the emission manifest; the axioms are the standard three, with named
   rows carried as hypotheses of a trust inventory; the toolchain and library pins are in the
   manifest; the axioms are also walked on the raw objects.
6. The three programs are three emissions with their own copies of shared types. Every fact
   that crosses a program boundary is stated on bytes (account data, instruction data, return
   data). Constants are emitted with their values and checked against the pinned value by hash.

Also agreed: one path from instruction bytes to the headline is composed end to end on the
emitted definitions before any breadth.

Credit of the two-transaction proof that rule 3 does not carry to Aspis (a loss of credit for
that proof's rows, not a regression of Aspis, which never had them in its closure): every closed
row of the Pool ledger (they rest on native tests, Kani and transcription packets); the
semantic-terminal gates emitted without the deployed features and what was proved on them; the
sampler models from rewritten crates; the transcription of `composition_parts`; the hand model
of `close_checkpoint`, which was owed and never built; consumer theorems of the hand-written
library models.

## 3. What a clean emission is

All of the following, for each of the three programs, on the candidate commit:

- One Charon run and one Aeneas run (Charon 454586e9, Aeneas 0d21a9ec, unpatched) rooted at the
  program's entry, at the configuration of rule 1, with `-abort-on-error` exit 0.
- The raw output compiles against the translator's own Lean library with zero edits: no regex
  adaptation, no shim, the generated external templates as they are.
- No Aspis-named bodiless declaration, checked by script. With this tool pair a function that
  fails but is called by a translated body becomes an axiom with no error, so exit 0 is not
  enough.
- Per crate, every function with a body in the Charon output is emitted or listed by name as not
  emitted with the reason.
- The silent-fault checks, each first shown to fire on a planted case: no write through a
  reversed mutable iterator; no write through a copied box in a dependency crate; no translated
  body that reaches a mutable account handle (section 5).
- Every site where the Solana build compiles different Aspis code from the translated host build
  is a runtime-boundary call, the allocator, the entry point, or test code unreachable at the
  deployed features. No arithmetic, parsing, transcript or Merkle code differs by target.
- A fidelity run that is not a proof: the recorded devnet payments, accepted and rejected, are
  executed through the emitted definitions and reproduce the Rust's decisions and intermediate
  values; every Merkle parent digest and transcript digest is compared between the host build
  and the Solana build; fixtures are generated by script from the devnet run.

## 4. Rewrite rounds

A rewrite changes no output, no error value or its position, no account write or its order, no
format, constant or check. Each round is gated against the frozen programs: identical verdicts
on the 156,704 corrupted proofs, identical prover output, the replayed payments and redirect
attempts, and compute measured on the built program with the per-function change recorded.
Where a round leaves the built programs byte-identical to the frozen ones, the on-chain gates
hold without rerunning. Panic locations (file, line, column) are stored in the built program, so
a rewrite keeps line counts and name lengths where it can.

Compute limits (the soundness lead's defaults, adopted by the lead; not the owner's numbers): a
round stops and reports if it adds more than 1 percent to the heaviest measured case (1,262,410
at the freeze) or more than 5 percent to a rewritten function; more than 2 percent cumulative
needs the owner; the working target is about 300 compute units per rewritten function.

Functions that an on-chain emission reaches are rewritten on the on-chain side and reused
verbatim by the prover side; functions only in the client scope are the privacy lead's.

## 5. The account write boundary

Finding (evidence/aspis-extraction-20261112/pool/README-stage2b.md): a write to account data or
lamports through the SDK's mutable handle has no form this translator accepts, and in the forms
that translate the emitted Lean omits the write. The two-transaction proof covered no state
change of either program: its writing Pool handlers and `close_checkpoint` stayed open.

Decision (owner, section 1): the writes are confined to a few private functions, accepted as a
named class. Wording agreed with the soundness lead: a standard-library and SDK row instantiated
at a listed call site, carried in the proofs as a named hypothesis of the trust inventory, not
as a global axiom. Its contract is stated on bytes: after the call the account's data equals the
old data with the given bytes at the given offset, or its lamports equal the given value; every
other field and every other account is unchanged; a failed borrow is an error return with
nothing changed.

Form, checked by a tool that is shown to reject planted violations: one SDK borrow of the
mutable handle of one account, then one assignment or `copy_from_slice` whose destination and
source are parameters. No arithmetic, no branch on data, no loop, no read, no second account.

Gates: the boundary functions are the only route to the mutable handles (source and emission
agree); no handler reads account data after its first write; the order of writes per handler
equals the frozen handler's; tests compare the full data and lamports of every account after the
frozen handler and the rewritten one, rejections included; the devnet run includes a rejection
at a check that follows a former write point; the exact text and line count of every boundary
function goes in the freeze record.

The class does not cover Aspis code that contains logic. The prover's untranslated shells (the
timing record, secret wiping, the wrapper of the check function) are not SDK-only and are a
separate list for the owner.

The hash call. `SolanaDigest::digest_into` keeps its direct call of the runtime's SHA-256 (three
lines; the SDK's wrapper costs 24,618 compute units more per payment). It is an item of the same
kind, under the same form check, with both realisations named in its row: the runtime call on
Solana, the SDK's `hashv` in the translated host build. The owner asked on 12 November whether
to go back to the SDK call; the lead and the soundness lead recommended keeping the direct call.

## 6. State of the translation on 12 November

Records: evidence/aspis-extraction-20261112/ (`onchain/`, `pool/`, `native-library/`, `audit/`).

- Verifier program: one whole-program run at the deployed configuration covers 714 functions;
  684 translate and elaborate against the earlier library. Against the translator's own library
  the raw output had 73 errors, 44 after the first two rewrites. Those two (shift amounts typed
  `u32` in 19 functions; `CM31::inv` calling the base inversion directly) are on `aspis-next`
  and leave all three built programs byte-identical to the frozen ones.
- Pool program: first emission ever. Of 438 functions in scope 354 translated and elaborated; 43
  were rejected, including three of the four instruction handlers. Rewrites are in progress in a
  scratch copy; none is applied.
- Prover (privacy lead's record): with the same unpatched pair 1,051 declarations translate and
  about 92 do not, including all proving entry points; a large constant that stopped the Lean
  compile is rewritten on `aspis-next`; the text after it had never been compiled.
- Not complete on any of the three. No proof work has started.

## 7. The Lean library

The generated Lean is compiled against the translator's own library (Lean 4.36.0-rc2, Mathlib
9d581dfff2e4; built on the host, evidence/aspis-extraction-20261112/native-library/). The
objects of the two-transaction proof stay as that proof's record.

The Aspis model theorems (ASPIS-FAILURE-BOUND.md) imported 1,451 modules, 38 of them tied to the
two-transaction proof's translated code. By their declaration-level dependency closure the two
theorems use nothing from those 38 except seven model-level definitions. The carried set is made
from the two-transaction proof's sources by the soundness lead's recorded scripts: import lines
replaced, named declarations dropped, some modules omitted, small base modules and one module of
empty namespaces added; the originals are untouched. Under Lean 4.32.0 the model chain compiles
on the carried set with the old objects off the search path; the two theorems depend on
`[propext, Classical.choice, Quot.sound]`; their printed statements are byte-identical to those
before the change; no carrier or omitted module is in their import closure. In the chain itself
only import lines changed.

The port to Lean 4.36.0-rc2 is in progress. Its rules: no text before a declaration's `:=`
changes (checked over the diffs); no `sorry`, no new axiom, no raised limit; a kernel recursion
or memory failure is inspected and the proof changed, with the avoided reduction recorded. A
declaration of the vendored polynomial package that the new Mathlib declares with the same
statement is removed in favour of Mathlib's, recorded with both statements. The ported tree will
live in the repository beside the chain with a per-module manifest (hash of the original, of the
trimmed text, of the ported text, and the edit list).

## 8. Open for the owner

- The prover's untranslated shells and the third-party crates its emission leaves without bodies
  (the SHA-256 implementation, the entropy source and supporting crates): the privacy lead is
  preparing one list in the form of section 5.
- Whether the privacy lead may delete its superseded build output on the build host.
