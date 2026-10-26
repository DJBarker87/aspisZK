# CPT contract preflight — stopped at the required contract gate

Target not yet established. L094/L095/L096/L180 deployed delta: **zero**.
Branch: `codex/cx-cp-runtime3-20261026`. No push or merge.

## Exact contract gap

The task explicitly says: “If the contract does NOT describe the game this way,
STOP and report the exact gap, because changing the game is an owner decision.”
That stop condition is reached before creating `CPT_Game.DeployedPairExecution`.
The requested contract is
`docs/research/100bit-spend-path-20261013/design/SECURITY-CONTRACT-20261021.md`.
Its complete two-transaction section is lines 77–101. Its operative description,
lines 79–83, is:

> The additive `OraclePortHeadlineFrozen2PerAttempt.final_soundness` targets
> `OraclePortFrozen2.dV_frozen2`, including checkpoint save and authenticated
> resume between batch 0 and batch 1. Its source premise is the newly targeted
> `OraclePortFrozen2Join.AcceptedRunJoin D rust`; it retains the original
> `StoredCarrierBinding D rust P runtime` and adversary query-count hypothesis.

This supports the two-stage checkpoint model. It does not supply exact wording
for the following proposed experiment fields:

| Requested field | Missing statement in the binding contract |
| --- | --- |
| Entry/execution association | The original `e1` and `e2` are the runtime entry projections of TX1 and TX2, rather than independently quantified entries. |
| Bank lineage and adjacency | TX2 loads the state left by TX1 on one bank lineage; no intervening transaction touching the protected key beyond the proposed law's `next`. |
| Physical account identity | TX1 slot 2 and TX2 slot 6 denote the same physical verifier CP public key, with a shared map relating their local cell labels to that key. |
| Parent success | TX1's *final parent transaction* succeeds, including runtime checks after the accepted native adapter call. |
| Ordered source association | The supplied CPP bank actions are exactly the relevant actions of these transactions in source order; the recorder is their physical event projection. |

“Authenticated resume” does not by itself specify physical-account identity,
final parent settlement or the permitted interleavings. Lines 99–101 explicitly
call this a “conditional model endpoint” and leave the “frozen-source
accepted-run join and runtime/carrier binding” open. The referenced
`DV-TWOTX-20261021.md` likewise leaves the runtime binding/source joins open;
it does not fill the physical experiment fields above.

The current task's lead ruling supplies the intended interpretation in prose,
but also expressly requires checking that interpretation against this contract
and stopping on a gap. I have not treated the ruling as an implicit amendment
that overrides its own stop condition. No claim is made that the intended
experiment is mathematically invalid; the missing item is its authoritative
contract specification and precise scope.

## Further boundary that the experiment cannot silently hide

Ordinary-key eligibility also needs the runtime fee-signature and durable-nonce
owner interpretations. `CPS_Ordinary.of_flags` states these explicitly;
`CPS_EntryFlags.writer` and `CPS_Ordinary.owner` derive only the source flags
and owner. The binding contract does not mention fee payers or durable nonces.
This eligibility cannot silently become another experiment field or trust item.
Likewise `CPS_BankRecorder.events` is proved for its supplied source action list,
not an independently established physical validator trace. A structure field
asserting that identity would specify an association, not prove its concrete
source refinement. These distinctions must survive any owner amendment.

## Before/after, validation and freeze

Before: the existing `T2R_Top.deployed` and conditional
`CPS_SourceTop.correlated` remain unchanged. After: identical statements and
carriers; no CPT theorem, experiment, premise deletion, non-vacuity construction
or new assumption. `CPR_DataPersistence.TwoTransactionLaw` remains unadopted.
No existing proof receipt is claimed as a newly checked result.

Read the mandatory root security/proof rules, common/local rules, historical S2
handoff/plan/diagnosis/interface, route-B addendum, SInt2/CPS/CPR handoffs,
runtime proposal, binding contract and two-transaction model design. Inspected
the source/root interfaces for the missing associations. Historical abbreviated
S2 paths resolve under `docs/research/100bit-spend-path-20261013/`.
`CPT_PREFLIGHT.json` pins the contract, referenced design, root and CPR/CPS
sources at the inspected revision. This is a static statement audit only.

Lean attempts **0/100**, Kani **0/10**; no host scope, dependency build, package
replay, Rust/SBF job or new theorem. Exact target, exit, wall, RSS, swap and
axioms fields are recorded as not applicable in the JSON because no formal
job ran. Budget is **not exhausted** and the whole-budget completion rule is
**not satisfied**: the explicit contract-gap stop condition precludes dependent
proof work, and unchanged replay would not resolve a contract decision.

No shipped source, cfg(kani) harness, existing Lean module, other prefix,
session A worktree, toolchain, feature, wire format, key, wallet or funds changed.
No ELF rebuild trigger. Inherited artifact pins, not reproduced:

- default `f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4`
- devnet `63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299`
- Pool `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548`

Next concrete deliverable: an owner-approved binding-contract clarification
specifying the fields above, including the permitted interleavings and how final
parent success enters the failure experiment. Then encode the named experiment
with exact field-local quotes, retain the runtime law as one explicit named
hypothesis, and prove source/ordinary-key interpretation rather than concealing
those obligations in the experiment. The law-only CPT root and joint accepted-
pair non-vacuity remain undelivered. The 100-bit release target remains open.
