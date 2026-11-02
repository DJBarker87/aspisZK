"""Exact proof-only normalization; raw emission is archived, never compiled."""
from pathlib import Path
import json,hashlib
D=Path('evidence/pv-b3p6-20261028');R=D/'resume18'
raw=(R/'std569-range-next/generated/Funs.lean').read_text()
s=raw.replace('import Std559.Types','import PV_B3P_Std559Types227\nimport PV_B3P_StringBound559227').replace('import Std559.FunsExternal','import PV_B3P_Std559External227').replace('core.option.expect_failed (toStr "`Step` invariants not upheld")','PV_B3P_Std559Nth227.core.option.expect_failed (toStr "`Step` invariants not upheld" PV_B3P_StringBound559227.step_message_bound)')
s+='\n#print axioms PV_B3P_Std569Range227.core.ops.range.Range.Insts.CoreIterRangeRangeIteratorImpl.spec_next\n#print axioms PV_B3P_Std569Range227.range_next\n'
p=D/'lean/PV_B3P_Std569KernelFuns227.lean'
if '--check'in __import__('sys').argv:assert p.read_text()==s
else:p.write_text(s)
assert (R/'std569-range-next/generated/Types.lean').read_text().replace('PV_B3P_Std569Range227','PV_B3P_Std559Nth227')==(D/'lean/PV_B3P_Std559Types227.lean').read_text()
x=dict(raw_sha256=hashlib.sha256(raw.encode()).hexdigest(),normalized_sha256=hashlib.sha256(s.encode()).hexdigest(),changes=['module imports; empty Types namespace reuse verified exactly','external sentinel qualification','sole diagnostic literal Prop bound supplied by existing kernel theorem','two summary-based print-axioms commands'],semantic_scope='own-1 proof normalization, NOT byte-identical emitted text; no Rust body, Step operation, carrier or Result-control rewrite',raw_emission_compiled=False,formatter_semantics_used=False,source_parity='FORMATTING-EVENTS-D569.json default Range spec_next; specialization/caller association separate')
(R/'NEXT-PROOF-NORMALIZATION-D569.json').write_text(json.dumps(x,indent=2)+'\n');print('exact next proof normalization checked')
