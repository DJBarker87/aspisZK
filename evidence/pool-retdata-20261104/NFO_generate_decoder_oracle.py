from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent;s=(E/'NFO_RawDecode.lean').read_text()
a=s.index('def\n  decode\n');b=s.index('\n#print axioms decode',a);body=s[a:b]
body=body.replace('def\n  decode\n  (bytes', '''def run
    (digest : Array U8 32#usize → Result (core.result.Result (Array U32 8#usize) atomic_statement.AtomicStatementError))
    (afterstate : Slice U8 → Result (core.result.Result pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1))
    (validate : pool_v1.pair_forest_terminal.PoolV1PairForestTerminalResultV1 → Result (core.result.Result Unit pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1))
  (bytes''')
body=body.replace('decode.closure','NFO_RawDecode.decode.closure')
for old,new in [('AspisR1TerminalDecoder.atomic_statement.decode_digest_canonical','digest'),('AspisR1TerminalDecoder.pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1','afterstate'),('AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.validate_result','validate')]:body=body.replace(old,new)
source='''import NFO_RawDecode
set_option autoImplicit false
noncomputable section
namespace NFO_DecodeOracle
open Aeneas Aeneas.Std Result ControlFlow Error AspisR1TerminalDecoder
'''+body+'''
theorem substitution (bytes : Slice U8) :
    run atomic_statement.decode_digest_canonical
      pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1
      pool_v1.pair_forest_terminal.validate_result bytes = NFO_RawDecode.decode bytes := rfl
#print axioms substitution
end NFO_DecodeOracle
'''
(E/'NFO_DecodeOracle.lean').write_text(source)
(E/'NFO_DECODE_ORACLE_GENERATION.json').write_text(json.dumps(dict(input_sha256=hashlib.sha256(s.encode()).hexdigest(),output_sha256=hashlib.sha256(source.encode()).hexdigest(),transformation='parameterize exactly digest, afterstate decoder, result validator; preserve byte operations/errors and closure identities'),indent=1)+'\n')
