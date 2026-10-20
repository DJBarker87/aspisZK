#!/usr/bin/env python3
"""Audit source empty reservation frame, whole constructor, and new/zip invariant."""
from pathlib import Path
import hashlib,json,re,resource,subprocess,sys,time
start=time.monotonic();tool=Path(__file__).resolve().parent;area=tool.parents[1];repo=tool.parents[4];ev=area/'evidence/cu-equivalence-20261019';sha=lambda b:hashlib.sha256(b).hexdigest()
subprocess.run([sys.executable,str(tool/'extract-rho-empty-reserve.py'),'--check'],check=True,capture_output=True)
origin=json.loads((tool/'rho-empty-reserve-source/origin.json').read_text());slices=(tool/'rho-empty-reserve-source/vec-used-slices.rs').read_bytes();assert sha(slices)==origin['slice_sha256'];assert b'Vec { buf: RawVec::new(), len: 0 }' in slices
for n in ['Types.lean','Funs.lean']:assert (tool/'rho-empty-reserve-generated'/n).read_bytes()==(area/'lean/AspisR1RhoEmptyReserve'/n).read_bytes()
targets={'AspisR1RhoEmptyReserve/Types':'rho-empty-reserve-types-a','AspisR1RhoEmptyReserve/Funs':'rho-empty-reserve-funs-a','CuSavingsRhoEmptyReserve':'rho-empty-reserve-proof-b','CuSavingsRhoEmptyReserveModel':'rho-empty-reserve-model-b','CuSavingsRhoHeapValues':'rho-heap-values-a','CuSavingsRhoAccumulatorCanonical':'rho-accumulator-canonical-b','CuSavingsRhoInitializationCanonical':'rho-initialization-canonical-a'}
results={};objects={};receipts={}
for module,attempt in targets.items():
 p=ev/attempt/'receipt.json';r=json.loads(p.read_text());assert r['exit_status']==0
 src=(area/'lean'/(module+'.lean')).read_bytes();assert sha(src)==r['source_sha256'];assert src==(ev/attempt/'source.lean').read_bytes()
 log=r['print_axioms_output'];assert 'sorryAx' not in log and 'error:' not in log
 ds=re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",log);assert ds
 for n,a in ds:assert set(filter(None,re.sub(r'\s+','',a).split(',')))<={'propext','Classical.choice','Quot.sound'},(n,a)
 assert r['cache_provenance']['selected_owner_objects']['Aeneas']['sha256']=='d3bfce818c2409992274bc1852aa00280cb7a8139465ef0bab674498e4cdc69d'
 objects[module.replace('/','.')]=r['object_sha256'];receipts[module]=r
 results[module]={k:r[k] for k in ['source_revision','source_sha256','object_sha256','features','command','exit_status','wall_seconds','peak_rss_kib','process_swaps','cgroup_swap_bytes','print_axioms_output']};results[module].update(attempt=attempt,receipt_sha256=sha(p.read_bytes()))
for module,r in receipts.items():
 for i in r['direct_imports']:
  if i['module'] in objects:assert i['sha256']==objects[i['module']],(module,i)
assert subprocess.check_output(['git','-C',str(repo),'diff','39c2971dd16c95858a4cfd2c9ae35da052eacfa9','--','crates','programs'])==b''
u=resource.getrusage(resource.RUSAGE_SELF)
report=dict(status='SOURCE_EMPTY_RESERVATION_FRAME_CONSTRUCTOR_AND_NEW_ZIP_INVARIANTS_CHECKED',candidate_complete=False,source_revision=subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD'],text=True).strip(),successes=results,std_source=origin,
 source_binding=['Exact safe std Vec.try_reserve_exact body self.buf.try_reserve_exact(self.len,additional), with opaque RawVec<T,A> field abstracted as B. Receiver lifting and original buf/len fields are checked against the pinned std source.',
 'Whole emitted wrapper is byte-unchanged. Its length frame holds for every raw-buffer computation, including reservation errors and outer failure/divergence; no frame, copying, success, or equivalence proposition is assumed of RawVec.',
 'Vec::new has zero length. A zero-length vector has unique empty logical contents regardless of buffer state. The new empty-input runtime projection erases capacity only; nonempty inputs retain an arbitrary separate computation and source_filled never takes that branch.',
 'Whole actual source_filled plus inherited resize and actual source QM31 Clone establish exact repeated-zero constructor contents. No heap child-content or success premise supplied to the constructor theorem.',
 'Whole actual BatchedWeights.new/zip using the whole source allocator yields initialState, Good raw bounds, canonical projection, counter zero and correct length from canonical caller input. That input is supplied by the source constructor/resume results; transaction composition remains separate.'],
 proved=['Source empty reservation frame and logical projection.','Whole heap-filled values and actual constructor canonical weights.','Whole actual new/zip starting arithmetic invariant without assumed heap-child length or success.'],
 remaining=['Tie allocation success to explicit sufficient-resource conditions and source allocator budget. No whole-program OOM equivalence claimed here.','Compose actual preparation/resume header, query/stage loops and transaction observables.'],
 audit=dict(command=[sys.executable,str(Path(__file__).resolve())],exit=0,wall_seconds=time.monotonic()-start,peak_rss_bytes=u.ru_maxrss if sys.platform=='darwin' else u.ru_maxrss*1024,process_swaps=u.ru_nswap,print_axioms='N/A receipt audit; exact per-target lists included'))
(ev/'RHO-INITIALIZATION-CANONICAL.json').write_text(json.dumps(report,indent=2)+'\n');print(report['status'])
