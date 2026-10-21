#!/usr/bin/env python3
"""Record unclosed component obligations and exact retained endpoint, not axioms."""
from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent.parent
endpoint=Path('docs/research/v8-r0-zk-20261009/lean/R1Z/PrivacyR1HeadlineDeployed.lean').read_bytes()
for name in ['endpoint-before.lean.txt','endpoint-after.lean.txt']:(E/name).write_bytes(endpoint)
(E/'endpoint.diff').write_text('')
(E/'endpoint-status.json').write_text(json.dumps(dict(status='not_specialized; target not established',before_sha256=hashlib.sha256(endpoint).hexdigest(),after_sha256=hashlib.sha256(endpoint).hexdigest(),premises_removed=[],premises_added=[],new_shipped_experiment=False,new_whole_run_joins=False,reason='No complete shipped simulator extraction/certificate or entropy/history adapter. Existing partial source checks are not full component certificates.'),indent=2)+'\n')
rows=[
 ('P6BuilderAdmission18','public compiler entry points to BuilderSource, including all public/common/value/conservation checks','BUILDER-CONT11-20261021.md, Stage 2 admission boundary; D101-D104','Not discharged by aggregate helper compilation; concurrent worker ownership retained'),
 ('P6CheckerRetry18','actual checker invocation and emit status, reject/abort classification and all eight source attempts, with retained oracle state','LOG D73.1; BUILDER-CONT11-20261021.md Scope','Local extracted checker exists; real checker/retry execution coupling remains open'),
 ('P6BorrowedMaterialIteration18','borrowed vector loops at arbitrary live prefix/capacity to owned collectors, preserving every scalar transition and error','PROVER-COMMIT17-20261021.md Stage 2; ProverCommitLoop17.run_related','One-cell Kani and generic induction do not instantiate the all-length source relation'),
 ('P6AssemblyNominalTransport18','Assembly17 nominal material/state/error types and six callees to Material14/Returned16 types and balancing schedule','PROVER-COMMIT17-20261021.md Stage 3; ProverCommitAssembly17.extracted_stages','Owned outer extraction is checked; nominal transport and borrowed-source preamble are not'),
 ('P6SerialisationTraversal18','complete source semantic/opening/multiproof iteration, sort/dedup, arbitrary Vec prefixes, framing, padding and rejection, to ordered List bytes','PROVER-COMMIT16-20261021.md; PROVER-COMMIT17-20261021.md Stage 1','Primitive/cell and one ordered-element checks do not establish full traversal'),
 ('P6EntropyGenerateTrace18','all up-to-16 96-byte OS draw paths, first valid grouping to SecP, retained cursor and immediate OS error','ProverCommitEntropy18; entropy18 Kani receipts','Model proved; first-success and OS-failure source paths checked; all-path source loop relation remains unproved'),
 ('PlatformEntropyLaw18','source OS draw law and possible failure, seed independence/freshness, fixed/preselected nonce path and durable-store failure behaviour','crates/aspis-prover/src/state_only_entropy.rs::generate and generate_for_mask_nonce','No source distribution law or fixed-event failure transport established; success symmetry alone is insufficient'),
 ('P6SimulatorOwned18','sim::sim_e public-seed input, tape/semantic/opening execution, collision failures and exact compact output','LOG D73.2; sim-charon-v1 receipt and sim-llbc-v1.json','Direct extraction has_errors=true; no promotion/Aeneas result exists'),
 ('SimulatorOracleHistoryAdapter18','sim::Coins frame/counter/stream requests, repeated nonzero draws, programming table duplicate/collision semantics and ordered observer suffix under the common oracle','crates/aspis-r1-cost-probe/src/sim.rs::Coins, CoinOracle, ProgramOne, programmed_hash','Fixed HOST_HASH seeded expansion cannot simply be called independent model coins; oracle idealisation/history transport must be explicit'),
 ('P6OuterAttemptPreamble18','durable reservation, context/binding/seed derivation, allocation/cloning, apply material and leaf salts before extracted outer material schedule','prover.rs::prove_masked_with_attempt; state_only_entropy.rs::reserve_and_build_pool_v1_pair_forest_mask_material_v1','Owned Assembly17 begins after reservation/seed/allocation and does not certify these operations')]
(E/'component-certificates.json').write_text(json.dumps(dict(status='Named unclosed contracts for follow-up; not Lean hypotheses, axioms, or accepted certificates',components=[dict(name=n,scope=s,evidence=e,remaining=r) for n,s,e,r in rows]),indent=2)+'\n')
report=Path('docs/research/v8-r0-zk-20261009/r1p-final/PROVER-COMMIT18-20261021.md')
s=report.read_text()
if '## Verbatim endpoint before' not in s:
 signature=endpoint.decode().split('theorem privacy_headline_deployed',1)[1].split(' := by',1)[0]
 declaration='theorem privacy_headline_deployed'+signature
 with report.open('a') as f:
  f.write('\n## Verbatim endpoint before\n\nNo specialization is claimed. This is the actual retained signature:\n\n```lean\n'+declaration+'\n```\n')
  f.write('\n## Verbatim endpoint after\n\nThe source remains identical; the requested specialized deletion has not been proved.\n\n```lean\n'+declaration+'\n```\n')
