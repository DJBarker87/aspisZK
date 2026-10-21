#!/usr/bin/env python3
"""Explicit audit owners, exact statements and conservative R22 classification."""
import hashlib,json,pathlib,re
ROOT=pathlib.Path(__file__).resolve().parents[2]
B=ROOT/'docs/research/100bit-spend-path-20261013'; OUT=B/'evidence/r22-total-20261021'
# These are source refinement endpoints, not every supporting algebra theorem.
SPECS=[
('S1','lean-candidates/s1-prepared-installed-meaning-20261020/sources/CurrentPreparedInstalledMeaning.lean','Caller success and inactive canonicality; residual callbacks/source join; Session A.'),
('S1','lean-candidates/s1-prepared-concrete-claim-20261020/sources/CurrentPreparedSourceMeaning.lean','Gamma/kappa/inactive canonicality and preparation success; Session A.'),
('S1','lean-candidates/s1-prepared-rho-meaning-20261020/sources/CurrentPreparedRhoMeaning.lean','Successful scalar/prepare or AfterQueries/Tail relation; source caller join; Session A.'),
('S1','lean-candidates/s1-claim-fission-sum-proved-candidate-20261020/sources/CurrentClaimSumTotal.lean','Canonical coefficients/parts and loop invariant; Session A candidate adoption.'),
('S1','lean-candidates/s1-early-return-powers-proved-candidate-20261020/sources/LoopPowersEarlyTotal.lean','Canonical x and state invariant; Session A candidate adoption/source pin.'),
('S1','lean-candidates/s1-zero-loop-powers-proved-candidate-20261020/sources/LoopPowersZeroCandidate.lean','Canonical x; Session A candidate adoption/source pin.'),
('S1','lean-candidates/s1-prepared-source-fromqm-20261020/sources/PreparedFromQmSourceBridge.lean','Literal carrier transport total; enclosing Prepared caller remains Session A.'),
('S1','lean-candidates/s1-prepared-indexed-bytes-20261020/sources/CurrentPreparedIndexedBytes.lean','Indexed-byte candidate total; adopted source/caller identity remains Session A.'),
('S1/S5','lean/ExtractedQM31SamplerCorrect.lean','Total fixed-block sampler; successful-output facts inherit it; actual caller provenance separate.'),
('S2','lean/S2ObserverOffRepin.lean','Arbitrary downstream tx1/error callbacks; no all-input checked execution.'),
('S3','lean-candidates/s3-s9-current-repin-20261020/S3InactiveExecutionBridge.lean','In-range row premise; row/inactive typed composition supplies it locally, optimized caller remains Session A.'),
('S3','lean-candidates/s3-s9-current-repin-20261020/S3InactiveModelBridge.lean','Range/read/row-value premises; typed row/inactive composition discharges row-value premise locally; Session A caller pin.'),
('S3','lean-candidates/s3-s9-current-repin-20261020/row-output-equation-v7-v1/sources/S3VariantRowCurrentSourceBridge.lean','Total current source-cut row value; full Weights pair still Session A.'),
('S3','lean-candidates/s3-s9-current-repin-20261020/row-loop-body-totality-v25-v4/sources/S3VariantRowLoopTotal.lean','Total current source-cut row; no full caller claim.'),
('S3','lean-candidates/s3-s9-current-repin-20261020/s3-row-inactive-compose-v1-20261020/sources/S3VariantInactiveComposition.lean','Total on Fin64 x Fin16; complete optimized caller remains Session A.'),
('S3','lean-candidates/s3-s9-current-repin-20261020/s3-pair-low-grouped-row-compose-v1-20261020/S3PairLowGroupedRowCompositionV1.lean','Low-input canonicality and source helper success; caller/from_fn/source joins remain Session A.'),
('S3','evidence/s3-loop0-outer12-full-helper-meaning-v1-20261020/sources/S3ActualLoop0Outer12CompositionV1.lean','Canonical low and successful actual grouped call; Session A.'),
('S3','evidence/s3-loop0-outer12-full-helper-meaning-v1-20261020/sources/S3ActualLoop1TotalPrefixV1.lean','Canonical arrays and prefix invariant; Session A.'),
('S4','lean-candidates/s4-four-dots-fixed-call-v2/sources/FourDotsFixedCallSuccessV1.lean','Success of enclosing fixed call; no full-call totality; Session A.'),
('S4','lean-candidates/s4-current-repin-20261020/FourDotsWideLimbCanonicalV1.lean','Layout conversion total; coordinate canonicality for arithmetic remains Session A.'),
('S4','evidence/s4-outer-fold-trace-v2-20261021/sources/S4OuterFoldTraceV2.lean','Outer success and canonical coefficient coordinates; Session A.'),
('S5','lean/ActualDecodeKStrictQM31Parser.lean','Total on fixed sixteen-byte arrays; strict limbs only on successful Some; payload framing separate.'),
('S5','lean/ExtractedCurrentReducer.lean','All stored U64 reducer inputs and all stored U32 multiplication inputs; concrete execution instance proved.'),
('S5','lean/ExtractedCurrentM31AddSub.lean','Canonical M31 operands; all-storage totality is false. Session A actual caller canonicality.'),
('S5','lean/ExtractedCurrentTowerAdd.lean','Canonical field operands; actual caller join remains Session A.'),
('S5','lean/ExtractedCurrentCM31Mul.lean','Canonical operands / graph equivalence; Session A caller canonicality.'),
('S5','lean/ExtractedCurrentQM31Mul.lean','Canonical operands; Session A caller canonicality.'),
('S5','lean/ExtractedCurrentQM31Exact.lean','Canonical operands; sampler composition proves one upstream discharge, frozen caller join remains Session A.'),
('S5','lean-candidates/s5-current-repin-20261020/sources/FinishDotDecodedProductTraceV1.lean','Successful finish plus count/canonicality trace; Session A.'),
('S5','lean/R22DecodeValueTotal.lean','Payload identity, count/offset/read bounds; framing caller proof missing.'),
('S5','lean/R22DecodeLoopTotal.lean','Payload framing and bounded loop; no success premise but not unrestricted totality.'),
('S6','lean/RepinS6First.lean','Decoder witness from checked caller success; tx1 and error callbacks arbitrary.'),
('S6','lean/RepinS6Ranges.lean','Numerical source bounds, not execution/refinement.'),
('S7','lean/Stage2ContinuationQueryAdvance.lean','Successful query/accumulation plus backend contracts; no all-backend totality.'),
('S7','lean/R22OverflowWorkerBackendObstruction.lean','Typed counterexample: backend zero may be fail integerOverflow.'),
('S8','lean/S8FrozenRow.lean','Explicit iterator/read/canonicality/cadence hypotheses; complete caller discharge absent.'),
('S8','lean/R22BatchedPushTotal.lean','Selected-row index/raw/canonicality premises; global cadence/counter caller missing.'),
('S8','lean/R22BatchedValueTotal.lean','Canonical raw-row / reducer preconditions where stated; complete caller source join missing.'),
('S3/S9','lean-candidates/s3-s9-current-repin-20261020/S3S9CurrentSourceModel.lean','Mathematical source-shaped classification/factorization; not total extracted execution.'),
('S7/S8','lean/R22Stage2LeafTotal.lean','Constant totalities; dynamic accessors need index bounds. Next consumer r22_opening_total.'),
('S7/S8','lean/R22Stage2OpeningTotal.lean','Index below22 and proof length at least28359; caller guards must supply independently.'),
('R20/P6','lean/ASQ8Normalization.lean','Accepted normalization/decoding Lean facts; unconditional harness safety lives in named P6 certificates.'),
('R20/P6','lean/ASQ8PoolHandoff.lean','Successful normalization/stripping Lean composition; P6 byte pipeline certificates separate.'),
]
TOTAL={
'fromQmSource_success','toBytesSource_success','installed_indexed_toBytes','sample_total',
'source_refines','current_reduce_mod','current_mul_mod','current_wrapper_mod',
'foldExecution_success','reduceExecution_success','reduceExecution_canonical','reduceExecution_mod',
's2_row_result_total','s2_row_result_value_current','s2_variant_row_inactive_grouped','toLimbs_actual_value'}
FORCE_OTHER={'first_eq_historical','roundtrip_result','reuse_decoded','current_reducer_eq',
'generatedCrossFragment_eq','generated_mul_graph','decode_eq_wordTower'}
PURE_FILES={'RepinS6Ranges.lean','S3S9CurrentSourceModel.lean','R22OverflowWorkerBackendObstruction.lean'}
rows=[]
for cone,rel,residual in SPECS:
 p=B/rel;txt=p.read_text();namespace=''
 for m in re.finditer(r'(?m)^(?:theorem|lemma)\s+(\S+)',txt):
  end=txt.find(':=',m.end());sig=txt[m.start():end].strip();name=m.group(1)
  nss=re.findall(r'(?m)^namespace (\S+)',txt[:m.start()]);namespace=nss[-1] if nss else ''
  form='OTHER';why='Result transport, mathematical property, or support lemma; no unconditional extracted success.'
  if name in TOTAL or (p.name=='R22Stage2LeafTotal.lean' and name.endswith('_total') and '(index :' not in sig and '(indices :' not in sig and '(values :' not in sig):
   form='TOTAL';why='Outer checked success for every typed input; see exact signature. Internal helper totalities are not additional caller cones.'
  elif p.name not in PURE_FILES and name not in FORCE_OTHER and (
      re.search(r'[({]\s*(?:h\w*|trace|fieldCanonical|hinv)\s*:',sig) and
      (re.search(r'\bok\b|success|[Tt]otal|Meaning|Canonical|AfterQueries|Trace',sig))):
   form='ACCEPTED-ONLY';why='Explicit success, canonicality, range, trace or callback premise. Local domain totality is allowed but not every input of the machine carrier.'
  if name=='reuse_decoded': form='ACCEPTED-ONLY';why='Explicit same-byte decode success; downstream tx1 remains arbitrary.'
  rows.append({'cone':cone,'path':str(p.relative_to(ROOT)),'line':txt.count('\n',0,m.start())+1,
  'theorem':namespace+'.'+name if namespace else name,'signature':sig,'form':form,'reason':why,
  'residual':residual,'source_sha256':hashlib.sha256(txt.encode()).hexdigest()})
(OUT/'audited-statements.json').write_text(json.dumps(rows,indent=2,ensure_ascii=False)+'\n')
print(len(rows),'audited owner statements',{k:sum(r['form']==k for r in rows) for k in ('TOTAL','ACCEPTED-ONLY','OTHER')})
