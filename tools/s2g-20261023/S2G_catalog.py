"""Emit the child inventory; unresolved entries never authorize a native stub."""
from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parents[2];D=R/'docs/research/100bit-spend-path-20261013';E=D/'evidence/s2g-20261023'
rows=[]
def row(child,contract,lean,source,status,missing):
 rows.append(dict(child=child,kani_contract=contract,lean_implication=lean,source_theorems=source,status=status,missing_theorem=missing,native_children_field_closed=False))
row('decode','Ok(statement) implies input.len=1880 and the SAME complete statement validates; Err unrestricted; no native frame',
 'AspisR1.S2G.decode_contract; AspisR1.S2G.Children.decoder_contract',
 ['AspisR1.S2A.InstalledCuts.decoded','AspisS2OwnedStage1.SourceInstallation.decoder_validated','AspisR1TerminalDecoder.DecoderSuccess.decode_success'],
 'pure installed value implication checked; Kani template disabled',
 'native decode_public_statement_box on the original borrowed slice refines S2G.decode with field-preserving full statement/Box/Result carrier, exact ProgramError, allocation/abort and state/effects; no independent successful decode premise')
row('validate','Ok implies exact actualValidator(statement)=Ok; for SAME decoded statement success is derived, not assumed',
 'AspisR1.S2G.validate_contract; AspisR1.S2G.decode_contract',
 ['AspisS2OwnedStage1.SourceInstallation.decoder_validated','AspisR1TerminalDecoder.DecoderSuccess.decode_success_validated'],
 'pure installed value implication checked; Kani template disabled',
 'native validator on that full decoded statement refines actualValidator and its exact error map/state, with read-only argument/heap/allocator frame on admitted inputs')
row('candidate','Ok(bytes) implies actual 688-byte encoder on SAME full afterstate returns IDENTICAL bytes; Err unrestricted',
 'AspisR1.S2G.candidate_contract',
 ['AspisS2OwnedStage1.SourceInstallation.actualEncoder','AspisR1.S2A.InstalledCuts.encoded'],
 'pure installed value implication checked; Kani template disabled',
 'native encode_pool_v1_pair_verified_afterstate_v1 afterstate refines actualEncoder on CurrentCarrier.toDecoderAfterstate, including exact rejection and all state/read-only effects')
row('first','Ok(cp) implies exact current candidate.tx1 with SAME statement public projection, public/proof/split/cp and observer None; NO cp length claim',
 'AspisR1.S2G.first_contract',
 ['AspisS2OwnedStage1.SdkReference.Installation.first_success','AspisR1CurrentCaller.FirstComposition.first_current_prepared_new','AspisR1.MultiproofConeFrozen2Stage.both_batches'],
 'wrapper value implication checked; whole-child native contract missing',
 'for ALL admitted reached first_decoded calls, concrete vops/currentDigest and source candidate.tx1 reify to SAME value and ordered effects; instantiate exact parser, batch0, ten query calls and checkpoint writer with S1/S3-S6/S9 provenance; retain all rejected prefixes and allocation/abort paths')
row('second','No enabled stub: requires actual tx2_authenticated(public,proof,checkpoint,SolanaDigest,None) full Result/state/effect refinement',
 'no proved enclosing second statement/instance in inspected tree',
 ['AspisR1.CheckpointBytes5Join.success_conditioned_checkpoint_stage_join','AspisR1.CheckpointBytes5Decision.decision_success_join','AspisR1.MultiproofConeFrozen2Stage.both_batches','AspisR1.S7JoinQueryRows.query_rows_exact','AspisR1.S8JoinFrozenScan.parsed_y1'],
 'missing whole-child theorem; predecessors only',
 'same checkpoint/public/proof source tx2_authenticated refines resume, batch1, twelve query callbacks and finish with exact returned Result and full ordered queries/state; derive S1S7S8StateProvenance and all concrete callback instances, not merely matching roots or accepted booleans')
row('SolanaDigest','Reified one-read returns actual D.digest(parts) and appends precisely (parts,digest); reached continuation receives that prefix',
 'AspisR1.S2G.Digest.contract; AspisR1.S2G.Digest.reached_call',
 ['AspisR1.CheckpointBytes5Effect.run_read','AspisR1.CheckpointBytes5Effect.run_bind'],
 'reified interpreter implication checked; native digest stub disabled',
 'pinned native SolanaDigest::digest/hashv on SAME ordered byte parts reifies to read parts and exact backend D.digest, then satisfies the retained per-call ROM/consistency law for all reached calls, including prefixes of rejected transactions; runtime query/log/rollback interpretation retained')
row('copy','requires len(dst)=len(src)=1768, i<1768, expected=src[i]; modifies dst[0..1768]; ensures dst[i]=expected',
 'AspisR1.S2G.CopyImplication.selected_byte; AspisR1.S2G.CopyImplication.other_cell; AspisR1.S2G.Copy.contract',
 ['AspisR1.S2C.copy_exact_byte','AspisR1.S2C.copy_other_cell','AspisS2OwnedStage1.SdkReference.CopyLoop.copy_in_place_total'],
 'Kani proof_for_contract and stub_verified consumer passed; owned/model implication checked',
 'bind exact native SDK guard data region and SAME returned cp to safe disjoint source/destination slices and owned SDK slot at copy cut; establish original geometry and continue through cleanup. Local verified slice stub itself has no missing callee proof')
row('drop_checkpoint','reuse existing S2C_checked_vec_drop empty-write contract ONLY for its checked Vec len/capacity1768, no-op SBF dealloc substitution and valid disjoint owners',
 'AspisR1.S2C.cleanup_metadata and cleanup_counters are conditional compositions, not owner implementations',
 ['AspisR1.S2C.cleanup_metadata','AspisR1.S2C.cleanup_counters'],
 'reused bounded owner check; S2E stateful callback unfilled',
 'actual valid returned Vec with its actual capacity, compiler implicit destruction and frozen allocator dispatch consumes SAME owner once, yields exact native/reference allocator state and preserves required original accounts/lamports/Rc/oracle fields')
row('drop_statement','reuse existing S2C_checked_box_drop empty-write contract ONLY under checked actual statement layout and dealloc substitution',
 'AspisR1.S2C.cleanup_metadata is conditional on ownerStep/frame laws',
 ['AspisR1.S2C.cleanup_metadata'],
 'reused bounded owner check; S2E stateful callback unfilled',
 'actual SAME Box<full Statement> implicit destruction consumes owner once and refines S2E drop_statement with exact allocator/frame effects, on admitted runtime provenance/dispatch; no fictitious cleanup suffix on abort')
row('validate_asq8','no enabled success stub; normalization byte identity is not authentication or ASF8 reconstruction',
 'AspisR1.OraclePortJoinSplitASQ8.pool_handoff has P6Normalization/success/suffix premises only',
 ['AspisR1.OraclePortJoinSplitASQ8.pool_handoff','AspisR20Request.ASQ8Normalization.success_bytes'],
 'missing authenticated validate_asq8 whole-child theorem',
 'for same program/full accounts/ASQ8 request native validate_asq8 returns SAME Validated(full statement,proof_length) or SAME error/state, deriving Clock/PDA/ownership/policy/reconstruction/validation/candidate-prefix facts and preserving reached hash/borrow/cleanup events')
row('public','no enabled stub; requires full ASF8 forest-statement encoder, bytes1880, both variants, SAME complete statement',
 'semantic/payment projection theorems do not assert full ASF8 serializer equality',
 ['AspisR1TerminalDecoder.CallerBridge.encoder_eq','AspisR1PublicPreparation.RepinS6First.reuse_decoded'],
 'missing full forest encoder native/installed statement',
 'native encode_pool_v1_pair_forest_terminal_statement_v1(statement) refines concrete S2E.public full Vec including complete serialization, errors/allocator/state. Payment216 encoder_eq or semantic-public projection is insufficient')
row('emit','no enabled stub; requires constructed result validation/encoding plus exact reached set_return_data(nonempty_bytes)',
 'no proved complete emit_result statement/effect instance in inspected tree',
 [],'missing emit_result whole-child theorem',
 'native emit_result on SAME statement constructs SAME result fields, validates/encodes exact result bytes/magic/length and performs exactly its reached return-data/log effects; earlier Err emits no nonempty suffix and preserves earlier verifier queries')
row('clear_return_data','no enabled stub; actual set_return_data(&[]) is a runtime event before validate_asq8',
 'no proved native syscall effect instance in inspected tree',
 [],'missing concrete runtime syscall port',
 'actual set_return_data([]) step refines concrete S2E.clear_return_data with exact appended syscall event/return-data state and account frame under pinned runtime premises; effects of later rejection/abort/rollback explicit')

# Pin exact source statements used as owner/predecessor citations (read-only).
sources={
 'S1':'lean-candidates/s1-prepared-installed-meaning-20261020/sources/CurrentPreparedInstalledMeaning.lean',
 'S3':'evidence/s3-loop0-outer12-prefix-retention-v1-20261020/sources/S3ActualLoop0Outer12PrefixRetentionV1.lean',
 'S4':'evidence/s4-candidate-total-local-values-v1-20261022/sources/S4CandidateTotalLocalValuesV1.lean',
 'S5':'lean-candidates/s5-stage2-dot-residual-composition-20261020/sources/Stage2FinishPairing.lean',
 'S6':'lean/RepinS6First.lean',
 'S9':'evidence/s9-focused-side-updates-root-v1-20261022/sources/S9SourceSideUpdatesRootV1.lean',
}
for p in ['lean/MultiproofConeParserTotal.lean','lean/MultiproofConeFrozen2Stage.lean','lean/MultiproofConeP6Frozen2Stage.lean','lean/CheckpointBytes5Join.lean','lean/CheckpointBytes5Decision.lean','lean/S7JoinQueryRows.lean','lean/S8JoinFrozenScan.lean','lean/ExtractedDecoderCallerBridge.lean','lean/ExtractedTerminalCallerBridge.lean','lean/ExtractedTerminalDecoderSuccess.lean','lean/S2C_Cleanup.lean','lean/OraclePortJoinSplitASQ8.lean']:
 sources[p]=p
pins={k:dict(path=p,sha256=hashlib.sha256((D/p).read_bytes()).hexdigest(),validation='read-only complete statements; existing evidence reused, not replayed or adopted as a whole child') for k,p in sources.items()}
(E/'contracts.json').write_text(json.dumps({'schema':'s2g-child-contract-catalog-v1','status':'PARTIAL; no concrete native Children instance','all_children':rows,'sources':pins,'new_native_Required14_fields':[]},indent=2)+'\n')
print('catalog:',len(rows),'children including nested digest; native whole fields closed:0')
