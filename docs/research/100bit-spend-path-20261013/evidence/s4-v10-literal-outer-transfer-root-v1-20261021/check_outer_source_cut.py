from pathlib import Path
import re, json, hashlib
raw=Path(__file__).parent/'dependencies/V10GeneratedFuns.lean'
adapted=Path(__file__).parent/'sources/S4V10LiteralOuterTransferRootV1.lean'
s=raw.read_text();start=s.index('def fast_dots.four_dots\n');decl=s[start:s.index('\nend AspisR1FastDotsMinimalFixedCallsV10',start)]
body=decl.split('  := do\n',1)[1].replace('fast_dots.four_dots_one','literalV10Helper ops').strip()
t=adapted.read_text();start=t.index('def literalV10Outer');end=t.index('\ntheorem literal_outer_eq_wrapper',start)
actual=t[start:end].split(':= do\n',1)[1].strip()
assert body==actual,'outer body differs beyond named child-operation substitution'
assert body.count('literalV10Helper ops')==4
print(json.dumps({'status':'PASS','raw_source_sha256':hashlib.sha256(raw.read_bytes()).hexdigest(),'adapted_source_sha256':hashlib.sha256(adapted.read_bytes()).hexdigest(),'raw_declaration_sha256':hashlib.sha256(decl.encode()).hexdigest(),'ordered_helper_calls':4,'substitutions':{'fast_dots.four_dots_one':'literalV10Helper ops'},'scope':'exact emitted candidate outer body; not adoption or concrete raw Ops binding'},indent=2))
