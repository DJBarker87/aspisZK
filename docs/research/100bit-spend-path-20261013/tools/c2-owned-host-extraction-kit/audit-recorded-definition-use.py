#!/usr/bin/env python3
"""Read/hash exact source-use slices. Generates JSON only; never invokes Lean.

Selections are a source-review proposal, not an inferred dependency graph or an
elaborated split. Exact public theorem syntax and original context are retained
for review; no reduced model or arbitrary semantic boundary is constructed.
"""
from pathlib import Path
import argparse,gzip,hashlib,importlib.util,json
ROOT=Path(__file__).resolve().parents[5];BASE=ROOT/'docs/research/100bit-spend-path-20261013';E=BASE/'evidence/c2-recorded-current-audit-20261018'
sha=lambda b:hashlib.sha256(b).hexdigest()
def module(n,p):
 s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
SPEND={
 'AspisFormal.Pool.V7PairLeafOccupancy':['Digest','PairLeaf','PairLeaf.secondSentinel','PairLeaf.Valid','PairLeaf.selectedOccupied','PairLeaf.selectedCommitment','PairLeaf.SelectedSlotIsSpendable'],
 'R1InputWitnessCore':['Relation'],'R1AppendNode':['frozenEmpty'],'R1AppendPath':['step','pathPrefix'],
 'R1SpendAppendBinding':['outputPair','AppendBinding'],'R1SpendRelation':['Witness','recipientCommitment','changeCommitment','variantOutput','Rspend','Wspend']}
MERKLE={
 'R1Merkle32Path':['Byte','Digest','Children','childByte','nodeBytes','nodeInput'],'R1Merkle32Leaf':['Byte','leafInput'],
 'R1MerkleTable':['digestDecidableEq','@instance:20','Nodes','lookup','walk'],'R1MerkleLeafRecovery':['Byte','LeafData','Leaves','lookupLeaf','recover'],
 'R1MerkleNodeCodec':['readChildren','parse'],'R1MerkleLeafCodec':['Byte','LeafData','parse'],'R1MerkleRecordedLog':['Byte','Log','nodes','leaves'],
 'RawByteCollisionTargets':['fixed','trailing','child','pred'],'RawByteCutRecovery':['cut'],'RawByteCutStability':['recoverAt'],
 'R1MerkleIndexGeometry':['slots','foldedIndex'],'R1MixedLeafEncoding':['C1Slot','C2Slot','C1','C2'],
 'R1MixedLeafDecoder':['decodeC1Slot','decodeC2Slot','decodeC1','decodeC2'],
 'R1TypedRecoveredWords':['C1','C2','C1Slot','C2Slot','zeroC1','zeroC2','queryLeaf','querySlot','decodeC1At','decodeC2At','c1Value','c2Value'],
 'R1LiteralTypedWords':['C1Word','C2Word'],'R1FoldedRecoveredWord':['Wide','Folded','foldedSlot','zeroFolded','wordOfPacked']}
SAMPLER={
 'R1TranscriptView':['Message','Value','Challenge','liftChallenge'],'R1DuplexSamplers':['plain','initial','reseeded'],
 'R1QuerySampler':['chain'],'R1QuerySamplerBridge':['sampler'],
 'R1UnifiedSampler':['Prefix','roundCount','stateOf','absorb','messageValid','invalid','liftQuery','samp'],
 'R1LiteralTranscript':None}
SUPPORT={
 'AllAddressCollisionTrace':['firstReads_eq_card_finiteSupport'],'OracleProgramRecording':None,'R1TraceTable':None,'OracleProgramReplay':None,
 'RawCutTranscriptRun':None,'RawCutProverCompiler':None,'C2RecordedExperimentConstruction':None,'R1GenericNoHit':['chooseWitness']}
EXTRA_PROOFS={
 'CanonicalCutEnrichedTranscript':['erase_enrichMessage','erase_enrichRounds','erasePrefix_enrich','sampler_enrich_eq'],
 'RawCutWordsFromView':['verifier_reads_in_experiment','recorded_transcript_eq','frameFromView_eq','buildWords_eq_actual_cuts']}
def build():
 inv=module('inventory',BASE/'tools/j1-integrated-declaration-repin.py');parser=module('parser',Path(__file__).with_name('model-command-parser.py'))
 z=(E/'candidate-closure.json.gz').read_bytes();g=json.loads(gzip.decompress(z));p=json.loads((E/'proposal.json').read_text());bz=(E/'definition-use-base-sources.json.gz').read_bytes();b=json.loads(gzip.decompress(bz))
 def parse(s):return parser.commands(s,inv.lean_tokens,inv.canonical)
 groups={};selections={}
 initial={c['source_module']:[d['exact_command']['qualified_name'] for d in c['selected_definitions']] for c in p['selected_definition_core_candidates']}
 # Original proposal names are fully qualified; resolve by exact qualified name.
 for label,selection in [('initial_twelve',initial),('spend_relation',SPEND),('merkle_typed_recovery',MERKLE),('actual_sampler',SAMPLER),('recording_replay_compiler',SUPPORT),('retained_bridge_proofs',EXTRA_PROOFS)]:
  names={};count=0
  for m,wanted in selection.items():
   n=g['fresh_sources'][m];assert sha(n['source'].encode())==n['source_sha256'];ds=parse(n['source'])
   if wanted is None:keys=list(ds)
   else:
    keys=[]
    for w in wanted:
     k=next((k for k,d in ds.items() if k==w or d['qualified_name']==w),None)
     assert k is not None,(m,w);keys.append(k)
   names[m]=keys;count+=len(keys);selections.setdefault(m,set()).update(keys)
  groups[label]={'source_interfaces':len(names),'selected_commands':count,'selection':names}
 assert groups['spend_relation']['selected_commands']==19
 assert groups['merkle_typed_recovery']['selected_commands']==62
 assert len(selections)==43
 sources={}
 for m,keys in sorted(selections.items()):
  n=g['fresh_sources'][m];ds=parse(n['source'])
  sources[m]={'source_path':n['path'],'source_sha256':n['source_sha256'],'original_imports':n['imports'],'selected_commands':{k:ds[k] for k in sorted(keys)},'commands_not_selected':[k for k in ds if k not in keys]}
 base={}
 for m,n in sorted(b['modules'].items()):
  assert sha(n['source_text'].encode())==n['source_sha256'],m
  base[m]={'source_sha256':n['source_sha256'],'source_path':n['source'],'origin':n['origin'],'all_command_hashes':{k:{f:d[f] for f in ['qualified_name','kind','declaration_token_sha256','signature_token_sha256','context_command_history_sha256']} for k,d in parse(n['source_text']).items()}}
 final=sources['C2RecordedExperimentConstruction']['selected_commands'];theorems={k:v for k,v in final.items() if v['kind']=='theorem'}
 assert list(theorems)==sorted(['row2_constructor','word_from_actual_cuts','public_and_acceptance','firstReads_eq'])
 return {'classification':'READ_ONLY_DEFINITION_USE_FRONTIER_NO_FORMAL_ACCEPTANCE','git_source_revision':g['git_revision'],'candidate_closure_gzip_sha256':sha(z),'corrected_proposal_sha256':sha((E/'proposal.json').read_bytes()),'base_source_subset_gzip_sha256':sha(bz),'base_export':{k:v for k,v in b.items() if k!='modules'},'groups':groups,'source_interfaces':sources,'current_base_source_providers':base,
 'accounting':{'original_broad_candidate_modules':295,'original_unsupported_import':'AspisV8R19.R572SequentialWordMass','initial_core_interfaces':12,'spend_additional_interfaces':6,'merkle_additional_interfaces':11,'actual_sampler_additional_interfaces':6,'program_support_additional_interfaces':8,'unbundled_selected_source_interfaces':43,'absolute_minimum_Lean_files':'NOT_ESTABLISHED: compatible declarations could be bundled, but this has not been generated or elaborated.','lower_bound_under_one_interface_per_source_module':43,'closed_few_target_executable_refresh':'NOT_DEMONSTRATED'},
 'preservation_requirements':[
 'All four final theorem statements, proof bodies and original namespace/section/context syntax are pinned; no Lean split has been produced or accepted.',
 'Rspend retains actual canonical public shape, InputWitnessCore.Relation, integer balance, change commitment, variant output and AppendBinding; Wspend remains the actual ExactTowerBase.M31Exact witness.',
 'NodeCodec.parse and LeafCodec.parse retain exact re-encoding equality guards, actual recorded-log filterMap, lookup/walk and decoder/default value definitions.',
 'LiteralTranscript.samp still calls actual UnifiedSampler.samp; retain stateOf, validity, absorb, invalid, liftQuery and actual duplex/query sampler definitions. Current Public/sigma cores alone do not supply this.',
 'Keep actual SemanticPublicWire.parsePublic, protocol Witness/relation/decoder, GenericNoHit.chooseWitness and full prover+verifier compiler experiment; no arbitrary relation, hash/sampler boundary, zeroC2 or on-chain-counter-only log witness.',
 'Do not copy UnifiedSampler.Public into a fresh core: current exact R1UnifiedSamplerPublic already supplies that qualified declaration.',
 'RawCutWordsFromView.frame_read, its private firstCell_mem support and buildWords_eq_full are outside the selected final-four proof cone; they are not refreshed or newly accepted.',
 'Generated deriving instances, anonymous MerkleTable instance public name, private mangled names, inferred binders and typeclass context require exact inverse/name audit and elaboration before any executable split claim.',
 'Unused proof-only opens and context commands cannot be silently discarded: retained command hashes include original context syntax, not a proof that changed imports elaborate identically.'
 ],'remaining_frontier':[
 'Spend and Merkle named-definition selections are traced; complete inferred/typeclass/private-name closure and exact minimal imports remain unchecked.',
 'The actual sampler adds six source interfaces; transcript datatype deriving instances and sampler imported constant identities must be rebound to the final current producer closure.',
 'Replay/compiler support adds eight source interfaces; private replay_apply identity must be preserved or mapped explicitly.',
 'The final6110-module C snapshot (commit17f8f2b38) is available and contains no RawCut objects. This supplement exports read-only source pins from the final215 workspace, not an adopted import overlay or a claim to have revalidated the full6110 closure.',
 'No source-equivalent few-target core patch has been generated or checked; the 295-target graph is not authorized for execution.',
 'Actual Rust Backend::c2 / Commitment::build owned-witness execution bridge remains OPEN; restoring this conditional recorded model would not establish that witness, packing, salt path, custody or checkpoint obligations.'
 ],'new_Lean_jobs':0,'new_formal_results':0,'production_changes':0}
def main():
 a=argparse.ArgumentParser();a.add_argument('--check',action='store_true');args=a.parse_args();out=E/'definition-use-frontier.json';data=(json.dumps(build(),sort_keys=True,indent=2)+'\n').encode()
 if args.check:assert out.read_bytes()==data,'frontier report mismatch'
 else:out.write_bytes(data)
 print(json.dumps({'status':'PASS_READ_ONLY_SOURCE_USE_AUDIT','spend_commands':19,'merkle_commands':62,'selected_source_interfaces':43,'small_executable_refresh':'NOT_DEMONSTRATED','new_Lean_jobs':0,'new_formal_results':0,'report_sha256':sha(data)},sort_keys=True))
if __name__=='__main__':main()
