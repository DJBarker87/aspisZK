from pathlib import Path
import json
E=Path(__file__).resolve().parent;R=E.parents[1];p=json.loads((E/'RPz3_source-plan.json').read_text());out=[]
for d,a in [('replay-dry2-20261026','RPz_001'),('replay-dry2-20261026','RPz_247'),('replay-dry3-20261026','RPz2_016'),('replay-dry3-20261026','RPz2_213')]:
 f=R/'evidence'/d/a;r=json.loads((f/'receipt.json').read_text());x=p['modules'][r['module']]
 out.append({'original_receipt':str(f.relative_to(R)/'receipt.json'),'receipt':r,'full_errors':(f/'stdout.log').read_text(),'current_selected_source':x['source'],'current_selected_hash':x['sha256'],'source_changed':list(r['source_hashes'].values())!=[x['sha256']],'retry':'only eligible when source changed; unchanged source not retried','axioms_qualification':'sorryAx in failed elaboration is diagnostic and not an accepted proof'})
(E/'RPz3_inherited-failures.json').write_text(json.dumps(out,indent=2)+'\n')
