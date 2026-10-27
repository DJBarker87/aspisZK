"""Inventory selected producer declarations without treating text as equivalence."""
from pathlib import Path
import json,hashlib,re
B=Path(__file__).resolve().parent
R=B.parents[1]
# Reuse only the pure parser functions, never the prior script's write actions.
s=(R/'evidence/extraction-repro2-20261027/XRb_compare.py').read_text()
exec(s[s.index('def digest'):s.index('inv={')])
paths={
 'cohort_Types':R/'docs/research/100bit-spend-path-20261013/lean/bridge-tx1-e5c186ba3-20261016/AspisR1PublicPreparation/Types.lean',
 'cohort_Funs':R/'docs/research/100bit-spend-path-20261013/lean-candidates/s1-prepared-claim-carrier-bridge-20261020/sources/AspisR1PublicPreparation/Funs.lean',
 'historical_Types':R/'evidence/extraction-repro2-20261027/XRb_historical_raw_Types.lean.txt',
 'historical_Funs':R/'evidence/extraction-repro2-20261027/XRb_historical_raw_Funs.lean.txt',
}
inv={k:{'path':str(p.relative_to(R)),'sha256':digest(p.read_bytes()),'bytes':p.stat().st_size,'declarations':declarations(p)} for k,p in paths.items()}
for k,v in inv.items():
 for d in v['declarations'].values():d.pop('text')
(B/'XRc_cohort_inventory.json').write_text(json.dumps({'normalization':'comments/attributes/whitespace removed; no semantic equality inferred','coverage':'ALL declarations in both selected producer files, a conservative superset of uses; proof-term reachability not inferred','inputs':inv},indent=2)+'\n')
# Keep the actual complete top statement; no wrapper is called premise removal.
top=R/'lean/Rc10_Top.lean'
for tag in ['BEFORE','AFTER']:(B/f'XRc_Top.{tag}.lean.txt').write_bytes(top.read_bytes())
ledger=R/'design/PREMISE-LEDGER-20261025.md'
(B/'XRc_recount.json').write_text(json.dumps({'target':'AspisR1.Rc10_Top.deployed','top_sha256':digest(top.read_bytes()),'ledger_sha256':digest(ledger.read_bytes()),'before_after_identical':True,'method':'Unchanged actual top and ledger; split quantified atomic families, preserve shared witnesses and T/P/G/C, deduplicate aliases including L185=L159','removed':0,'added':0,'changed':0,'delta':{'T':0,'P':0,'G':0,'C':0},'absolute_recount':'not newly performed','nonvacuity':'No new joint witness; partial extraction is not non-vacuity','axioms':'N/A: no new top theorem'},indent=2)+'\n')
print({k:len(v['declarations']) for k,v in inv.items()})
