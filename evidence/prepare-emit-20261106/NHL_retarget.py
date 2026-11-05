"""Canonical nominal/opaque-call retarget. Raw emitted inputs remain untouched."""
from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent
raw=E/'NHL_emitted/prepare/Funs.lean';s=raw.read_text();body=s[s.index('def verifier.candidate.prepare\n'):s.rindex('\nend NHL_Actual')]
body=body.replace('def verifier.candidate.prepare\n','def prepare (ops : AspisR1CurrentCaller.Ops)\n',1)
mapping={
 'aspis_core.r0.heap.filled':'ops.op1',
 'compact.expand_semantic':'ops.op10','compact.expand_values':'ops.op11',
 'verifier.candidate.wide_view':'ops.op5','r1_semantic.verify_observed':'ops.op9',
 'verifier.Prepared.new':'ops.op8',
 'core.result.Result.map_err':'AspisR1CurrentCaller.core.result.Result.map_err',
 'verifier.Error.Insts.CoreConvertFromCodecError':'(AspisR1CurrentCaller.verifier.Error.Insts.CoreConvertFromCodecError ops)',
 'compact.LOGICAL_SEMANTIC':'(AspisR1CurrentCaller.compact.LOGICAL_SEMANTIC ops)',
 'compact.LOGICAL_Y1':'AspisR1CurrentCaller.compact.LOGICAL_Y1',
 'compact.OFF_SEMANTIC':'16#usize',
 'compact.OFF_Y1':'(AspisR1CurrentCaller.compact.OFF_Y1 ops)',
 'compact.OFF_INACTIVE':'(AspisR1CurrentCaller.compact.OFF_INACTIVE ops)'}
for a,b in mapping.items():body=body.replace(a,b)
header=s[:s.index('namespace NHL_Actual')]
header=header.replace('import Aeneas\nimport NHL_Actual.Types\nimport NHL_Actual.FunsExternal','import NHF_Prefix\nimport NGK_COMBINED_IMPORT')
header+='namespace AspisR1.NHL_EmittedPrepare\nopen AspisR1CurrentCaller\n'
(E/'NHL_EmittedPrepare.lean').write_text(header+body+'\nend AspisR1.NHL_EmittedPrepare\n')
(E/'NHL_RETARGET_PREPARE.json').write_text(json.dumps({'raw_sha256':hashlib.sha256(raw.read_bytes()).hexdigest(),'mapping':mapping,'nominal_types':'reuse existing AspisR1CurrentCaller owners; no new carrier types','body_sha256':hashlib.sha256(body.encode()).hexdigest(),'note':'Generated wrapping add retained. The theorem must justify its equality to the cohort checked add on concrete source constants.'},indent=1)+'\n')
raw=E/'NHL_emitted/tx1/Funs.lean';s=raw.read_text();body=s[s.index('def verifier.candidate.tx1\n'):s.rindex('\nend NHL_Actual')]
body=body.replace('def verifier.candidate.tx1\n  {H : Type}', 'def tx1 (ops : AspisR1CurrentCaller.Ops)\n  {H : Type} (prepareCall : Prepare H)',1)
mapping={
'verifier.candidate.parse_shape':'ops.op3','verifier.candidate.canonical_scan':'ops.op4',
'aspis_core.field.wide_exact.WideExact.ZERO':'(AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact.ZERO ops)',
'verifier.candidate.prepare':'prepareCall','verifier.Accumulator.new':'ops.op20',
'verifier.candidate.batch_merkle':'ops.op6','verifier.QueryGeometry.for_range':'ops.op19',
'verifier.BatchedWeights.new':'ops.op18','verifier.candidate.query_loop':'ops.op7',
'verifier.BatchedWeights.finish':'ops.op17','verifier.checkpoint':'ops.op16',
'compact.OFF_FOLDED_ROOT':'(AspisR1CurrentCaller.compact.OFF_FOLDED_ROOT ops)',
'compact.OFF_ROUND1':'(AspisR1CurrentCaller.compact.OFF_ROUND1 ops)'}
for a,b in mapping.items():body=body.replace(a,b)
header=s[:s.index('namespace NHL_Actual')].replace('import Aeneas\nimport NHL_Actual.Types\nimport NHL_Actual.FunsExternal','import NHL_EmittedPrepare')
header+='''namespace AspisR1.NHL_EmittedTx1
open AspisR1CurrentCaller
abbrev Prepare (H : Type) := aspis_core.digest.Digest32 H →
 aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public → Slice U8 → H →
 Option (verifier.Phase → Result Unit) → Array aspis_core.field.wide_exact.WideExact 29#usize →
 Result (core.result.Result verifier.Prepared verifier.Error ×
   Array aspis_core.field.wide_exact.WideExact 29#usize)
'''
(E/'NHL_EmittedTx1.lean').write_text(header+body+'\nend AspisR1.NHL_EmittedTx1\n')
(E/'NHL_RETARGET_TX1.json').write_text(json.dumps({'raw_sha256':hashlib.sha256(raw.read_bytes()).hexdigest(),'mapping':mapping,'nominal_types':'existing AspisR1CurrentCaller owners','body_sha256':hashlib.sha256(body.encode()).hexdigest()},indent=1)+'\n')
