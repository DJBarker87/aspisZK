"""Use the last authorized ID for the combined audit and focused closure in order.
39898 was refused before compilation; no final manifest has previously run.
"""
from pathlib import Path
import json,re,hashlib
L=Path('docs/research/v8-r0-zk-20261009/lean/R1Z');E=Path('evidence/pv-batch2-20261027/batch2e')
a=(L/'PV_B2_E_AuditCombined.lean').read_text();c=(L/'PV_B2_E_AuditClosure.lean').read_text();c=re.sub(r'^import [^\n]+\n','',c,flags=re.M)
s=a+'\n-- Focused two-row closure after the complete combined public-axiom audit.\n'+c
p=L/'PV_B2_E_AuditFinal.lean';p.write_text(s)
j=dict(target='R1Z/PV_B2_E_AuditFinal',attempt=39899,reason='39898 ordinary reservation refusal consumed the penultimate authorized ID, compiler_launched=false',combined_public_audits=len(json.loads((E/'AUDIT-PREFLIGHT.json').read_text())['public_declarations']),focused_closure=['PV_B2_E_AuditClosure.sampler_rows','PV_B2_E_AuditClosure.dictionary_observations'],same_receipt=True,separate_second_replay=False,full_privacy_endpoint_replay=False,source_sha256=hashlib.sha256(s.encode()).hexdigest(),blocked_fixture_gate='V258/V259/V260 universal original/copy/allocation and row predecessors remain open; ordered whole-prover fixture gate not run')
(E/'FINAL-AUDIT-PLAN.json').write_text(json.dumps(j,indent=2)+'\n')
print('final target',j['target'],'audits then focused closure; one receipt')
