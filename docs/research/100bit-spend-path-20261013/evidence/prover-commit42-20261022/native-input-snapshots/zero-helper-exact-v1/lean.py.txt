#!/usr/bin/env python3
"""Install only this job's new modules and run one assigned env J attempt."""
import subprocess,sys,os
from pathlib import Path
module,attempt=sys.argv[1:3]
wait_cap="--wait" in sys.argv[3:]
memory_gib=int(os.environ.get("PROVER_LEAN_MEMORY_GIB","8"))
assert memory_gib==8
assert 9400<=int(attempt)<=9799
rel=module.replace('.','/')+'.lean'
p=Path('docs/research/v8-r0-zk-20261009/lean')/rel
snapshot=Path(__file__).resolve().parent.parent/'lean'/'sources'/('attempt-'+attempt+'-'+module.split('.')[-1]+'.lean.txt')
snapshot.parent.mkdir(parents=True,exist_ok=True)
assert not snapshot.exists()
snapshot.write_bytes(p.read_bytes())
host='dombarker@100.108.41.90'
R='/home/dombarker/project-offloads/codex-cx-prover-commit42-20261022'
subprocess.run(['scp',str(p),host+':'+R+'/incoming.lean'],check=True,stdout=subprocess.DEVNULL)
code='''import hashlib,json,re,subprocess,time
from pathlib import Path
R=Path(%r);J=Path('/home/dombarker/project-offloads/aspis-joint-20261019')
rel=%r;attempt=%r;memory_gib=%r
p=J/'sources'/rel
assert rel in ['Query31ScanTypesOnly.lean', 'Query31ExplicitScanBody.lean', 'Query31ExplicitScanConcreteSteps.lean', 'Query31ExplicitListLoop.lean', 'Query31UnrolledDriverFirstStop.lean', 'Query31ModelScanCall.lean', 'Query31ModelDriverChain.lean', 'SelectorArrayMapRuntimeSlice.lean', 'TerminalStandardOperationModelsV1.lean', 'TerminalArrayFromFnModelV4Clean.lean', 'SelectorArrayMapSuccess.lean', 'QueryScanConcreteWordsDecoder.lean', 'Query31ConcreteWordsDriverChain.lean'] or rel in ['AspisR1GammaCaller/Types.lean', 'GammaCallerExplicitHelpers.lean', 'GammaCallerDigitsModel.lean', 'AspisR1Post25Sampler/Types.lean', 'AspisR1Post25Sampler/Funs.lean', 'ExtractedQM31SamplerIndexedCandidate.lean', 'IndexedCandidateGeneratedLoopBridgeV4.lean', 'IndexedCandidateOuterByteBridgeV13.lean', 'IndexedCandidateOuterByteOutputSuccessV5.lean', 'GammaCandidateLowQuotient.lean', 'GammaCallerRankModel.lean', 'AspisR1Post25SamplerIndexedAddSmallCandidate/Types.lean', 'AspisR1Post25SamplerIndexedAddSmallCandidate/Funs.lean', 'IndexedCandidateAddSmallGeneratedOneStepV1.lean', 'IndexedCandidateAddSmallLoopCanonicalV11.lean', 'IndexedCandidateAddSmallNatModelV1.lean', 'IndexedCandidateAddSmallWrapperNatModelV3.lean', 'GammaCandidateAddSmallHelpersRefine.lean', 'IndexedCandidateDecode8RetainedBridgeV3.lean', 'GammaCandidateDecodedFieldRank.lean', 'GammaCandidateTotalityV14.lean', 'IndexedCandidateOrdinarySampleBridgeV3.lean', 'IndexedCandidateOrdinaryRetainedBridgeV5.lean'] or rel.startswith(('AspisR1IndexInsert32/', 'AspisR1Publish32/', 'AspisR1Program32/', 'AspisR1ByteOrder32/', 'AspisR1Folded32/', 'AspisR1Opening32/', 'AspisR1SemanticInit28/','AspisR1EffectCallers27/','AspisR1CoinEffect27/','AspisR1CircleCaller25/','AspisR1SimControl21/','AspisR1SimFields20/','AspisR1SimSemantic20/')) or rel.startswith('AspisR1SimulatorConcat19/') or rel.startswith('AspisR1SimulatorInsert19/') or rel.startswith('AspisR1SimulatorCoin18/') or rel.startswith('AspisR1ProverAssembly17/') or rel.startswith('AspisR1ProverMaterial14/') or rel.startswith('AspisR1ProverCollect10/') or rel.startswith('AspisR1ProverBalance9/') or rel.startswith('AspisR1ProverStep8/') or rel.startswith('AspisR1ProverCaller7/') or rel.startswith('AspisR1ProverCommitReference/') or rel.startswith('AspisR1ProverCommit/') or rel.startswith('AspisR1ProverLeaf/') or rel.startswith('AspisR1ProverStreams/') or rel.startswith(('AspisR1Environment35/','AspisR1Retry34/','AspisR1PublicSerializer34/')) or rel.startswith('AspisR1PublicNonce41/') or rel.startswith('R1Z/ProverCommit') or rel.startswith('R1Z/PrivacyR1HeadlineOrdered16') or rel.startswith('R1Z/PrivacyR1HeadlineDeployed') or rel.startswith('R1Z/PhaseWireOrdered16') or rel in ('R1Z/PrivacyR1FinalProtocolQuotient.lean','R1Z/PrivacyR1FinalProtocolCaller.lean','R1Z/PrivacyR1FinalProtocolCallerScope.lean','R1Z/PrivacyR1HeadlineCallerScope.lean','R1Z/PrivacyR1HeadlineOwned.lean','R1Z/PrivacyR1HeadlineOwnedClosed.lean')
p.parent.mkdir(parents=True,exist_ok=True)
if p.exists():
 q=R/'snapshots'/attempt/rel;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(p.read_bytes())
 o=J/'objects'/Path(rel).with_suffix('.olean')
 if o.exists():q.with_suffix('.olean').write_bytes(o.read_bytes())
p.write_bytes((R/'incoming.lean').read_bytes())
env=json.loads(Path('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/env/J.json').read_text())
paths=[J/'objects']+[Path(x) for x in env['LEAN_PATH'].split(':')]
deps=[]
seen=set()
def visit(m):
 if m in seen:return
 seen.add(m)
 r=Path(m.replace('.','/')+'.olean')
 o=next((d/r for d in paths if (d/r).exists()),None)
 assert o,m
 deps.append((m,hashlib.sha256(o.read_bytes()).hexdigest()))
 q=J/'sources'/Path(m.replace('.','/')+'.lean')
 if q.exists() and (m in ['Query31ScanTypesOnly', 'Query31ExplicitScanBody', 'Query31ExplicitScanConcreteSteps', 'Query31ExplicitListLoop', 'Query31UnrolledDriverFirstStop', 'Query31ModelScanCall', 'Query31ModelDriverChain', 'SelectorArrayMapRuntimeSlice', 'TerminalStandardOperationModelsV1', 'TerminalArrayFromFnModelV4Clean', 'SelectorArrayMapSuccess', 'QueryScanConcreteWordsDecoder', 'Query31ConcreteWordsDriverChain'] or m in ['AspisR1GammaCaller.Types', 'GammaCallerExplicitHelpers', 'GammaCallerDigitsModel', 'AspisR1Post25Sampler.Types', 'AspisR1Post25Sampler.Funs', 'ExtractedQM31SamplerIndexedCandidate', 'IndexedCandidateGeneratedLoopBridgeV4', 'IndexedCandidateOuterByteBridgeV13', 'IndexedCandidateOuterByteOutputSuccessV5', 'GammaCandidateLowQuotient', 'GammaCallerRankModel', 'AspisR1Post25SamplerIndexedAddSmallCandidate.Types', 'AspisR1Post25SamplerIndexedAddSmallCandidate.Funs', 'IndexedCandidateAddSmallGeneratedOneStepV1', 'IndexedCandidateAddSmallLoopCanonicalV11', 'IndexedCandidateAddSmallNatModelV1', 'IndexedCandidateAddSmallWrapperNatModelV3', 'GammaCandidateAddSmallHelpersRefine', 'IndexedCandidateDecode8RetainedBridgeV3', 'GammaCandidateDecodedFieldRank', 'GammaCandidateTotalityV14', 'IndexedCandidateOrdinarySampleBridgeV3', 'IndexedCandidateOrdinaryRetainedBridgeV5'] or m.startswith(('AspisR1PublicNonce41.', 'AspisR1Environment35.', 'AspisR1Retry34.', 'AspisR1PublicSerializer34.', 'AspisR1IndexInsert32.', 'AspisR1Publish32.', 'AspisR1Program32.', 'AspisR1ByteOrder32.', 'AspisR1Folded32.', 'AspisR1Opening32.', 'AspisR1SemanticInit28.','AspisR1EffectCallers27.','AspisR1CoinEffect27.','AspisR1CircleCaller25.','AspisR1SimControl21.','AspisR1SimFields20.','AspisR1SimSemantic20.','AspisR1SimulatorConcat19.','AspisR1SimulatorInsert19.','AspisR1SimulatorCoin18.','AspisR1ProverAssembly17.','AspisR1ProverMaterial14.','AspisR1ProverCollect10.','AspisR1ProverBalance9.','AspisR1ProverStep8.','AspisR1ProverCaller7.','AspisR1ProverCommitReference.','AspisR1ProverCommit.','AspisR1ProverStreams.','AspisR1ProverLeaf.','R1Z.ProverCommit'))):
  for child in re.findall(r'^import (\\S+)',q.read_text(),re.M):visit(child)
for m in re.findall(r'^import (\\S+)',p.read_text(),re.M):visit(m)
deps.sort()
def reservation_total():
 caps=[]
 for c in Path('/sys/fs/cgroup').rglob('memory.max'):
  try:
   v=c.read_text().strip()
   if v!='max' and (c.parent/'cgroup.procs').read_text().strip():caps.append(int(v))
  except OSError:pass
 return sum(caps)
start=time.monotonic()
while reservation_total()+memory_gib*2**30>55*2**30:
 assert %r and time.monotonic()-start<600, ('reservation hold',reservation_total()/2**30)
 if time.monotonic()-start<1:print('Waiting for a capped Lean reservation; no compiler launched.',flush=True)
 time.sleep(15)
fp=hashlib.sha256(json.dumps(deps,sort_keys=True).encode()).hexdigest()
(R/('lean-'+attempt+'.json')).write_text(json.dumps(dict(module=rel,attempt=int(attempt),source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),deps=deps,deps_fingerprint=fp,deps_fingerprint_scheme="own-cone-transitive-objects-v2",memory_limit_mib=7000,cgroup_memory_max_gib=memory_gib),indent=2)+'\\n')
subprocess.run(['sh',str(R/'run-joint.sh'),attempt,rel[:-5],'J','7000',str(memory_gib),fp],check=True)
log=Path('/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence')/('out-'+attempt+'.log')
assert re.search(r'^exit=0$',log.read_text(),re.M), 'Lean compile failed: '+attempt
'''%(R,rel,attempt,memory_gib,wait_cap)
subprocess.run(['ssh',host,'python3 -'],input=code,text=True,check=True)
