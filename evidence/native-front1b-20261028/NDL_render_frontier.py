from pathlib import Path
import json
E=Path(__file__).resolve().parent;d=json.loads((E/'NDL_LEDGER_DELTA.json').read_text());closed=[r for r in d['members'] if r['status']=='CLOSED-local']
s='# NDL frontier bridges\n\n'+str(len(closed))+' of '+str(len(d['members']))+' representatives CLOSED-local ('+str(len(closed)-7)+' new, seven imported NDD); '+str(len(d['members'])-len(closed))+' OPEN. No composed closure. Headline AspisR1.RPx_Deployed.deployed: 100-bit per-attempt target not yet established. Native semantic transport is owner-approved P6/D188 trust reclassification.\n\nBudget use: '+json.dumps(d['budget_used'])+'. Receipts and exact source revisions/hashes: NDL_ATTEMPTS.jsonl and each attempt directory. All table NDD citations are read-only imports, not re-proofs.\n\n| Function | Rows | Status | Packet / exact remaining obligation |\n|---|---:|---|---|\n'
for r in d['members']:
 if r['status']=='CLOSED-local':t=r.get('domain','')+'; '+r.get('lean_theorem','')+'; '+r.get('lean_attempt','')+'; '+r.get('kani_attempt','')+'/'+r.get('negative_control','')+'; extraction '+r.get('extraction','')
 else:t=r.get('partial_evidence','')+'; '+r['obstacle']+' Lean: '+r.get('remaining_lean_only_obligation','')
 s+='| `'+r['function']+'` | '+str(r['dependent_rows'])+' | '+r['status']+' | '+t.replace('|','\\|').replace('\n',' ')+' |\n'
s+='\nFull NCZ validation on the own overlay refuses the changed merged report corpus; structural invariants pass. No authoritative ledger or snapshot was changed, and every composed row remains OPEN.\n'
(E/'NDL_FRONTIER_BRIDGES.md').write_text(s)
