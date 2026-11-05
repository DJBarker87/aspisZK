from pathlib import Path
import json
E=Path(__file__).resolve().parent
J=lambda n:json.loads((E/n).read_text())
W=lambda n,x:(E/n).write_text(json.dumps(x,indent=2)+'\n')
audit=J('NIG_final_audit/RESULT.json')
audit.update(combined='NIG_L080',raw_ax2='NIG_L082',scan='NIG_L082',fixture='NIG_L028',statements='NIG_L081',scope='focused coherent cached replay with NGK and RPx_Deployed.deployed; not a cold frozen release replay',receipt='NIG_L082/receipt.json')
W('NIG_AUDIT.json',audit)
closed=J('NIG_CLOSED.json')
for row in closed['functions']:
 row.update(combined_replay='NIG_L080',ax2='NIG_L082',scan='NIG_L082')
closed['model_exports']={
 'NHM_new':'NIG_Slots.NHM_new',
 'NHM_pair':'NIG_PairExport.NHM_pair',
 'NHM_finish':'NIG_FinishPacket.NHM_finish',
 'native_bridge_status':'OPEN; these exact model equations do not promote pair129 or finish115'}
W('NIG_CLOSED.json',closed)
d=J('NIG_LEDGER_DELTA.json')
d.update(evidence_audit='NIG_L082',model_exports_only=closed['model_exports'],open_edges='NIG_EDGES.json')
W('NIG_LEDGER_DELTA.json',d)
r=J('NIG_L082/receipt.json')
W('NIG_FINAL_RESOURCES.json',dict(
 budget=dict(kani_used=120,kani_limit=120,formal_used=80,formal_limit=80,extract_used=0,extract_limit=1),
 combined='NIG_L080',statements='NIG_L081',audit='NIG_L082',
 source_revision=r['source_revision'],exit_status=r['exit_status'],wall_seconds=r['wall_seconds'],
 peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],limits=r['limits'],
 roots=audit['roots'],modules=audit['modules'],print_axioms='NIG_L081/stdout.log; raw ax2 NIG_L082/stdout.log; standard only',
 prelaunch_failures_not_counted=['NIG_L067 dependency NIG_PairShared missing','NIG_L075 dependency NIG_PairExport missing']))
