#!/usr/bin/env python3
"""Repair an owned unmatched-opacity input; retain the failed original attempt."""
from pathlib import Path
import json,copy
E=Path(__file__).resolve().parent
p=json.loads((E/'NMH_PLAN.json').read_text());old=json.loads((E/'NMH_E030_spec.json').read_text());r=copy.deepcopy(json.loads((E/'NMH_E006_spec.json').read_text()))
r['run']='NMH_E030';r['label']='verify-observed-opacity-repair';r['repairs']='NMH_E006: expected verifier::mark absent; actual reached r1_semantic::mark must be selected and checked opaque';r['basis']='Owned input repair from actual frozen call at r1_semantic.rs verify_observed. Exact prior configuration retained as failed E006; replace dead verifier::mark selector with actual semantic::mark. All NHR opacity checks retained, no removed expectation.'
for key in ['charon_command','aeneas_command']:
 r[key]=[s.replace('/NMH_E006_emitted/','/NMH_E030_emitted/').replace('crate::verifier::mark','crate::r1_semantic::mark') for s in r[key]]
r['configuration']['opaque']=[s.replace('crate::verifier::mark','crate::r1_semantic::mark') for s in r['configuration']['opaque']]
for v in r['opacity']:
 if v['path']=='crate::verifier::mark':v.update(path='crate::r1_semantic::mark',why='Actual frozen local mark callee; corrected dead verifier-mark expectation, still require reached declaration and Opaque body.')
r['configuration']['roots']=['crate::r1_semantic::verify_observed'];r['configuration']['charon_command']=r['charon_command'];r['configuration']['aeneas_command']=r['aeneas_command'];r['configuration']['opacity']=r['opacity']
assert not (E/'NMH_E030/receipt.json').exists()
(E/'NMH_RETIRED_WIRE_PROBE.json').write_text(json.dumps(old,indent=2)+'\n');(E/'NMH_E030_spec.json').write_text(json.dumps(r,indent=2)+'\n')
p['runs']=[r if q['run']=='NMH_E030' else q for q in p['runs']];p['owned_input_repairs']=[dict(failed_attempt='NMH_E006',replacement='NMH_E030',reason=r['repairs'],budget='Replaces unlaunched wire-record diagnostic; still at most30 Charon invocations')]
(E/'NMH_PLAN.json').write_text(json.dumps(p,indent=2)+'\n');cfg=json.loads((E/'NMH_E030.json').read_text());cfg['module']=r['label'];cfg['expected_time']='Changed actual mark opacity; cached optimized Charon, then Aeneas. Prior failed expectation retained.';(E/'NMH_E030.json').write_text(json.dumps(cfg,indent=2)+'\n')
print('E006 own-input failure retained; E030 corrects actual reached mark selector, same strict validation')
if __name__=='__main__':pass
