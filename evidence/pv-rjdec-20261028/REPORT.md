# Observation installation and V047 — D420 resume

**Target not yet established. Whole ledger rows removed: 0.**

Worktree exactly `/Users/dominic/ZK/.worktrees/pv-rjdec`, branch
`codex/pv-rjdec-20261028`, entry `11d5d0368be4678182ddd25a11a411175fb47a4f`.
Assigned IDs 61800–61899; 61897–61899 reserved for audits. The preceding report
is retained as `REPORT-before-D420.md`. Item (b) belongs to pv-own and is not
claimed or modified here. Existing RunJoin sources and all shipped Rust are
read-only; all new Lean modules use `R1Z.PV_RJDec_`.

## (a) Actual native observation installations — OPEN

No concrete native implementation/installation of `Runtime.disclosed` or
`Runtime.observerOracle` has been established. The source audit follows
`SourceConstructor.runtime`, `LedgerConstructor.runtime`,
`InstalledEndpoint.runtime` and the installed/joined/causal headline inputs.
They take observation functions as parameters. The deployed `devnet_spend`
client calls `RealR1_client::prove_for_proof_accounts`, writes `proof.bin` and
`statement.bin`, and returns JSON containing proof-account/publication data,
mask audit and elapsed time. Identifying that native observation with either
Runtime field requires an adapter and its complete law; a constructor name
or a similarly named verifier `Observer = Option<fn(Phase)>` is not that law.

`d420-native-installation-audit.json` records exact source blobs, hashes,
relevant lines and the native symbol search. This is source inspection,
**not a checked counterexample to the shipped program** and not proof that
an alternative adapter cannot be constructed.

PROVED lower interface/source facts are listed with their final validation
below. `RuntimeFields.execute_independent` proves that replacing the two
observation functions leaves `execute` unchanged. Its
`oracle_underdetermined` gives two different field values for the same source
execution interface; these are DATA examples, not proposed native decoders.
`SourceFields.fields`, `LedgerFields.fields` and `InstalledFields.fields`
check exactly which supplied functions the respective constructors forward.

`TotalExtension.cases_iff` decomposes the fixed decoder law for **all** Results
into success, every outer failure and divergence. `CommonCases.complete_pair`
then consumes the six resulting clauses, together with Common's unchanged
entropy/body/initial-state simulation hypotheses. It does not prove those
six native clauses. No unreachable-result extension was chosen silently.
The existing `Factor.exists_iff`, `ResultCases.fibres_iff` and pair criterion
remain the exact reachable-run failure/divergence-prefix obligations. No
native instance of those obligations is established. No post-world, query
prefix, rejected suffix, error, timing or other observation was discarded.

## Input parser work and the concrete decoder cohort

ParserR20 and ParserR12 remain complete emitted-input-parser source laws, not
ROMView decoder laws. The new small prefix/guard targets isolate early
source failure/divergence and length rejection without unfolding a large
recurrence. Their hypotheses and scope are printed in the combined audit;
they supply no native helper adequacy or observation installation.

The previous `JHb_DataRequest` import gap is resolved by its exact committed
retained source snapshot. Its SHA256 is
`3eaac8622d871eefc750067ee01d27d42ece23a1a54912f1d534be1a5193096c`, matching
both the predecessor source-closure pin and its historical Git blob.
The public/proof/checkpoint data and transfer-13 fibre prerequisites are built
privately; no other job's object was substituted. The 19 retained-source
resolutions and conventional-path alternatives are recorded in
`d420-resolution-alternatives.json`.

The attempted old concrete `JFs_PublicDecode` closure still reaches an
unresolved cohort: `JFu_PublicHeader` imports
`ExtractedTerminalDecoderSuccess`, whose transitive source needs
`AspisR1SelectedMaskProbe.Funs`/`.Types`. The exact tracked alternatives are in
`d420-decoder-cohort-gap.json`. No variant was selected and no object from that
unresolved cone was consumed. The inherited runjoin37 extractor disposition
is retained; no alternate extractor or manually edited emitted body was used.
This blocks that import route, not every possible new proof of the parser.

## (c) Actual native statement and V047 fibre — OPEN

The missing statement is still
`actual = AspisR1.PV_2TNV_PublicEncoding.x native_handle` for the **actual** native
statement and handle. No actual deployed Runtime or statement/handle constant
is constructed here. The transfer-13 public index is 13; the old index-zero
witness is not substituted.

PROVED lower consumer `PV_RJDec_V047Native.consume` supplies the original
`PV_2TNV_HeadlineFibre.fibre native_handle` to `PV_RJDec_V047.consume`. Its exact
remaining named premise is the full native statement equality above; its
conclusion is
`∃ w : PV_RJDec_V047.H.Instance, PV_RJDec_V047.H.public w = actual.1`.
`identification_iff` exposes both the public-component and handle-component
obligations. Neither component is erased or asserted as a proved native fact.

No joint wrapper execution theorem was proved. `FixturePdaRuntime base` is
not consumed by the mathematical consumer, is not discharged, and is not
added to T. Any implication involving the parked joint wrappers still needs
its explicit fixture-runtime and joint-proof binders.

## Boundaries and validation

Endpoint premises removed/added/weakened/changed: **0/0/0/0**. V038, V045,
V163, V165, V167 and V244 remain. The eight endpoint premise fields and the
three TrustItems (`entropy_law`, `entropy_kernel`, `observation`) are unchanged.
The complete observer/simulator, coupling, bad/query events, failure
independence, side channels, compiler-cohort, D188 and K-1/K-2 qualifications
retain their previous scope. Source-constructor checks and cached focused
replays earn no native or release-artifact credit.

**Fresh budget exhausted: 100 Lean attempts, 99 accepted / 1 rejected;
0 native scopes; 0 Kani; 0 VOID attempts.** Every ID 61800–61899 launched
exactly one compiler. The three reserved audits passed. The 61842 reservation
refusal launched no compiler; its same-ID retry followed the full cooldown.
Every admitted launch checked exit zero and `allowed:true` in the same shell
command as the scope. MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64,
Lean -M7000 throughout. No cap or prover limit was raised.

| ID | Exact target | Exit | Scope wall s | Peak RSS bytes | Swap |
| --- | --- | --- | --- | --- | --- |
| 61897 | `R1Z.PV_RJDec_D420Statements` | 0 | 2.69 | 4739510272 | 0 |
| 61898 | `R1Z.PV_RJDec_D420Axioms` | 0 | 2.01 | 4735287296 | 0 |
| 61899 | `R1Z.PV_RJDec_D420Replay` | 0 | 1.94 | 4735414272 | 0 |

Audit source revisions: 61897: `89022bfba27d24b2595a1c3871147f766258fbdf`, 61898: `89022bfba27d24b2595a1c3871147f766258fbdf`, 61899: `6591e115eaab6749723ed3c5926cb31ac5ad69bb`. No Lean source changed afterward.

All accepted printed axiom sets are subsets of propext, Classical.choice and
Quot.sound. Peak RSS over the fresh budget was **4739510272 bytes**;
all swaps were zero. Complete exact source pins, targets, dependency
fingerprints, commands, admission records, exits, wall times, RSS, swap and
axiom lines are retained in `receipt-618*.json`, `modules-618*.json` and the
original per-module output/time files. `d420-original-logs.json` hashes those
original files. `d420-own-validation.json` checks all accepted private sources,
objects and import fingerprints, including the retained predecessor objects.

Attempt 61866 was rejected at default simplifier recursion depth while
expanding the emitted afterstate decoder. It is not credited. The generator
now uses `ParserR15.source_chunk` and its already checked named `reference`;
that changed source passed as 61867, with unchanged limits. The failed Git
blob and original diagnostics are retained in `d420-failed-sources.json` and
`61866-00.out`. The other three generated prefix modules remain byte-identical;
the generator's `--check` passed. No unchanged failed source was rerun.

The missing constructor/caller objects were rebuilt privately, unchanged,
solely to check the observation forwarding and retained headline signatures.
No new helper-effect association for item (b) is claimed. The final generic
`PV_RunJoin_CausalHeadline` source remains staged but uncompiled after the
charged rejection consumed its slot; it is excluded from both final audits
and proof credit. The installed and joined headline signatures are audited.
This is a focused cached replay, **not** a frozen-manifest release replay,
new artifact-fidelity result or native implementation proof.

The initial inherited-cache preflight verified 2,764 project source/object
pairs, 5,802 import fingerprints, 5,673 external objects and 5,438 IR companions.
The final read-only preflight rechecks those pins. `d420-scope-sequence.json`
records disjoint launch intervals. `d420-local-input-corrections.json` records
compile-free staging/audit corrections. The exact commit list since entry is
`d420-commits.txt`; the final evidence-freeze commit follows its generation.
No other worktree, shared source/object, shipped source, wallet or account key
was edited; no extraction, Rust/native gate, ELF rebuild, push or merge ran.

## Next concrete deliverable

Construct and identify the two actual native observation adapters, including
their installed call sites. Prove both reachable full failure/divergence-prefix
fibres and the six fixed-decoder total Result clauses before supplying Common.
Then identify the actual native public record and commitment handle, prove
`actual = PV_2TNV_PublicEncoding.x native_handle`, and use the checked
`PV_RJDec_V047Native.consume`. Keep FixturePdaRuntime and joint wrapper proof
binders explicit wherever those wrapper implications enter. Items (a) and (c)
remain OPEN; item (b) remains with pv-own. Endpoint and whole-row removal: zero.
