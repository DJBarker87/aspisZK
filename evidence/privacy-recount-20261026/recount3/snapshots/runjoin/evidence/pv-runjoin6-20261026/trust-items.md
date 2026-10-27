# Proposed trust contract and P separation

`R1Z.PV_RunJoin_TrustItems d` has three field groups. The parameter `d`
remains explicit; no actual deployed native interpretation is claimed.
All carriers and quantifiers are in `PV_RunJoin_TrustItems.lean`, printed in
out-26811.log. This is an escalation for the owner, not adoption.

| Field | Exact statement | Carrier | Shipped location | Class | If false |
|---|---|---|---|---|---|
| entropy_law | `∀ context raw, d.law context raw = 1 / (Fintype.card Raw : ℚ)` | `Raw = Fin 2 → OracleAnswer`, 64 successful bytes; complete prior context | `crates/aspis-prover/src/state_only_entropy.rs:StateOnlyAttemptSecrets::generate_for_mask_nonce` / `getrandom::fill` | OS/kernel contract | biased/correlated masks can expose witness information; the claimed uniform conditional law no longer transports |
| entropy_kernel | `∀ c, d.nativeWeight c = PV_RunJoin_E1Joint.weight 128 d.law d.frame d.coordinates c` | SAME joint completion coins and residual world; 128 64-byte draws | same factory, reached from `crates/aspis-r1-cost-probe/src/RealR1_client.rs:prove_for_proof_accounts` | OS/kernel contract | correlations with prior draws, oracle, failures or schedules can defeat joint privacy even with uniform marginals |
| observation | `∀ c, d.nativeObservation c = d.extractedObservation c` | typed joint Observation: initial/final worlds, ordered (pre-world, tagged call) list, filesystem State, complete D159 observer payload | `RealR1_client.rs:prove_for_proof_accounts`, entire reached prover/callback/FS call graph, selected compiled x86_64 Linux binary | OS/kernel contract + toolchain + hardware | native effects or compiled/hardware observations reveal information absent from extracted execution; source privacy does not transfer |

The third field is native-to-extraction only. It contains no equality with
the privacy experiment, simulator, RunJoin, or privacy inequality. The P trace
obligation supplies extraction-to-security-model agreement. F3/F5/F6 source
trace simulation cannot be replaced by this trust item.

Five filesystem constructor clauses are one outcome family; time/workers
remain distinct constructors on the SAME world. `TrustOutcomes` proves exact
equivalence with the old eight-leaf Identity structure, with no availability
condition. That all-world primitive contract is NOT a field of T: only
execution observations are required at the endpoint. It does not prove the
actual native Identity instance.

Separate filesystem and complete-view projection equalities are derivable by
`observation_projection` from the typed joint observation record. Ordered call-trace projections retain
getrandom/open64/read/write/sync/close/time/worker outcomes, preventing
separate duplicate native trust hypotheses for those same observations.
They are deleted from T. Successful-byte uniformity does not imply joint
factorization. Joint observation equality does not by itself assert a probability law.
No claim of globally smallest axiomatic presentation is made: these are three
semantically distinct contracts, not a trick counting conjunctions as one.

## Options, both UNADOPTED

A would add `PV_RunJoin_AvailableOption.OsAvailable` as an extra trust
field or an explicit theorem premise:

```lean
∀ p, p.used.val < p.replies.val.length →
  ∃ after bytes, boundary.draw.fill p (Array.repeat 64#usize 0#u8) =
    .ok ((after,.Ok ()),bytes)
```

This is the prior in-capacity 64-byte OS-draw option; it excludes OS failure,
interpreter failure and divergence for those draws. It does not assert
nonzero seeds, E1, E2 or native/source association, and availability by itself
does not prove V038. It is absent from T and the new headline statements.
B would change the experiment/conclusion to feed the SAME public error signal
and full error observation to real and ideal, as in PublicFailureEndpoint.
It belongs in the statement, not in a hidden observation equality. It is absent.

## P obligations

P-selection: construct the actual `SourceSelectionContract.Data`; prove its
`PublicBinding`, with D162's selected caller and SAME compiled record.
P-admission: SelectedAdmission.Remainder's exact `compile_call`, `words`,
`publicCorr`, `admission` for those records. `row_call` is already a theorem.
P-runtime: install actual world initializer/account policy/native dictionary,
source hash/public inputs, complete decoders and ideal handler, on pinned
release/compiler/CPU carriers. A function of free data is not a concrete value.
P-source/ledger/fill: instantiate the checked candidate source/control lemmas
at that same runtime (including dictionary/source projections).
P-byte-blind: initial ledger independent of future raw tape and causal frames;
fault schedule is already definitional in LedgerBoundary, so not a trust item.
P-trace: for all adversaries/witnesses and SAME shared coin outside the UNCHANGED
bad event, extracted COMPLETE observation equals the security source experiment.
Includes joint L1/L2 F3/F5/F6; OS errors must be treated without silently adopting A/B.
P-release: coherent dependency closure replay, release byte/source identity,
compiler/flags and CPU pin, complete observer-carrier binding.

The concrete carrier binding is itself uninstalled P data: File must be
`PDict_FileCarrier.File`, Reply must be `PDict_World244.Reply`, with
constructor-preserving request/reply mapping, the same entropy positions and
file cursor, and the chosen native error/time/worker carriers. A generic `E`,
`File`, `Reply`, `Time`, `Worker` is NOT evidence that these equalities hold.
The ordered trace also needs its actual extracted producer/validity proof;
an arbitrary list of Call values is not an extracted execution. These are
P-runtime/P-trace, not additional trust items or claims of instance closure.
