# L159/L181 root-interface decision packet (lead, 2026-10-26)

Status: DECISION REQUESTED from the owner. No change adopted. Rc10_Top.deployed
is unchanged (byte-identical kernel statement checked by ARU_/ARV_).

## What twelve rounds established

1. The raw-join-or-collision event, the account recorder, queried-address
   consumers, the original-law cylinder factory, exact per-phase costs and the
   full adaptive-work charge are proved (ARQ_, ARS_, ART_, ARU_). The Q+34
   start charge and the zero-query margin 2^-108 - 6(1161^2+2965^2)/2^256
   - 2^-126 - 2^-454 > 0 stand with every term kept (ART_).
2. Two checked interface facts (ARV_, evidence/account-rejoin7-20261026):
   - ARV_NativeCostGap.obstruction: Rc10's `queries` premise bounds only the
     ByteProver P's eval length. The owner-approved adaptive game lets the
     adversary issue Q+1 ignored queries before TX2 without changing P's
     program, so P's bound cannot serve as the account experiment's work
     bound. Not an attack: a work-accounting interface fact.
   - ARV_OneTuple.obstruction: one native tuple does not support every
     partial-experiment world; the unsupported branch is exactly one that
     runtime admission excludes from the approved game.
   - ARU_RootRestriction.impossible_if_native: deleting `binding` while
     leaving `runtime` independently quantified contradicts the zero-query
     conjunct. So L181 cannot be closed by literal deletion.

## The proposed root (ARW_Root.deployed, being proved by account-rejoin8)

Relative to Rc10_Top.deployed, exactly these binders change:
- `(runtime : F3T_Runtime.Runtime)` and `(binding : StoredCarrierBinding ...)`
  are replaced by `(a : SCE_Experiment.Adversary A)` with
  `runtime := ART_Runtime.runtime (configuration) hashv copy allocator verifier a`,
  the deployed runtime image at a (D188 extraction / P6C_ refinement).
- `(P : ByteProver)` with `queries : ∀ H, (eval H P).1.length ≤ Q0+Q1`
  becomes P := the ByteProver induced by a, with
  `queries : ∀ H, (issued H a).length ≤ Q0+Q1` (a's total issued digest
  queries across both reached phases: the contract's definition of Q).
Everything else (carriers, failure event, constants Q+34 / Q+1161 / Q+2322 /
Q+2965, conclusion) is literal.

## Why this is a specialisation, not a weakening

The frozen3 headline quantified over an arbitrary ByteProver P and an
arbitrary Runtime tied to P by `binding`. The owner-approved experiment
(class G, two-transaction game, RuntimePersistence) defines the adversary as
the account adversary a interacting with the deployed runtime. Instantiating
runtime at the deployed image and charging a's own queries is the statement
for the deployed system. ARW_Conservativity (to be proved) shows that for an
adversary whose work is all through P with no adaptive choice, the new root
gives Rc10's conclusion with the same constants.

## What it would cost

- No new trust item. The deployed image rests on the existing D188 item.
- The headline's "per-attempt" unit is unchanged; Q now counts the
  adversary's issued queries, which is what SECURITY-CONTRACT already says.
- The ledger loses rows L159/L185 and L181 as atomic premises and gains none,
  but the top theorem's statement changes; that is why this is not booked as
  "premises removed" without the owner's approval.

## Recommendation

Adopt ARW_Root.deployed as the headline root once (1)-(4) in the account-
rejoin8 brief are proved and the before/after comparison is checked, with the
change recorded in SECURITY-CONTRACT as a statement amendment. Alternative:
keep Rc10 literal and accept that L181 is closed only by a `binding` proof for
an arbitrary Runtime, which ARU_ showed is contradictory in the zero-query
case; that alternative has no route.

## Amendment (lead, 2026-10-26, after ARW_)

The "deployed runtime image at a" in the proposed root is the ADMITTED
runtime: ARX_AdmittedRuntime, parameterised by the bank tuple, admission1/2,
the approved game and RuntimePersistence, with world range exactly the
executions the approved game admits. ARW_ showed the literal ART_Runtime term
ranges over a world the game excludes (accepted but unsupported RunView,
ARV_Poison.no_admission), so it is not the right image. The adversary a stays
arbitrary; constants and failure event unchanged. ARX_ (account-rejoin9)
proves the law equivalence on admitted worlds and the root; adoption still
awaits the owner.

## Status 2026-10-27: ARX_Root.deployed is proved

account-rejoin9 (ARX_, merged 680b10c65d) proved the proposed root with the
admitted runtime, standard axioms, exact margin unchanged, and unconditional
conservativity on the old pure-choice class at the admitted runtime. The
complete before/after declarations are in
evidence/account-rejoin9-20261026/ARX_ROOT_COMPARISON.md. recount11 is
producing the mechanical ledger for both roots and the draft contract
amendment. Decision requested: adopt ARX_Root.deployed as the headline root.

## Numbers (recount11, 2026-10-27)

Rc10_Top.deployed: actual 83T/12P/13G, deployment-inclusive 89T/16P/13G.
ARX_Root.deployed: actual 83T/11P/13G, deployment-inclusive 89T/14P/13G.
Removed: L159/L185, L181. Added atomic premises: none. Draft contract
amendment: design/SECURITY-CONTRACT-ARX-AMENDMENT-DRAFT-20261027.md.
