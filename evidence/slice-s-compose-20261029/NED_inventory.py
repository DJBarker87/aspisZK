from pathlib import Path
import json,hashlib,subprocess
E=Path(__file__).resolve().parent;R=E.parent.parent
L=json.loads((R/'evidence/native-ledger3-20261029/NDT_LEDGER.json').read_text())
S=json.loads((R/'docs/research/100bit-spend-path-20261013/design/VERTICAL-SLICES-20261029.json').read_text())['slices']['S']
claims={c['claim_id']:c for c in L['claims']};rows={f:next(r for r in L['rows'] if r['function']==f) for f in S['functions']}
edges=[]
for edge in S['internal_edges']:
 a,b=edge.split(' -> ');r=rows[a];o=next(x for x in r['caller_domain_obligations'] if x['callee']==b)
 sites=[c for c in r['callees'] if any(t.split('@')[0]==b for t in c['targets'])]
 edges.append(dict(edge=edge,caller=a,callee=b,obligation=o,sites=sites,classification='unreviewed actual call or conservative alternative',status='OPEN',certificate=None,obstacle='Needs same-call argument/domain, Result, state, ordered-effect and inner PhysicalInterpretation transport; no certificate inferred from local status.'))
(E/'NED_EDGES.json').write_text(json.dumps(dict(frozen_revision=L['frozen_revision'],slice='S',edges=edges),indent=1)+'\n')
(E/'NED_SCOPE.json').write_text(json.dumps(dict(branch=subprocess.check_output(['git','branch','--show-current'],text=True).strip(),revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),ledger_sha256=hashlib.sha256((R/'evidence/native-ledger3-20261029/NDT_LEDGER.json').read_bytes()).hexdigest(),slice=S,budget=dict(kani=40,lean=150),members=[dict(function=f,bridge_status=r['bridge_status'],selected_claims=[claims[k] for k in r['selected_claims']],named_hypotheses=r['named_hypotheses']) for f,r in rows.items()]),indent=1)+'\n')
print(len(edges),'edges;',len(rows),'members')
