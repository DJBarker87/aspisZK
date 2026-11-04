"""Final focused source/receipt and rendered-output checks; no regression replay."""
import json,hashlib,subprocess,re
from pathlib import Path
P=Path(__file__).resolve().parent;B=P.parent
pins=json.loads((P/'pins.json').read_text())['revisions'];status=json.loads((P/'status-audit13.json').read_text())
for r in status['D653']['focused_receipts']:
 b=subprocess.check_output(['git','show',pins['own2']+':'+r['source_path']])
 assert hashlib.sha256(b).hexdigest()==r['source_sha256'] and r['exit']=='0' and r['accepted']
source='evidence/pv-b3p6-20261028/resume18/lean-92898/receipt/stdout.log'
b=subprocess.check_output(['git','show',pins['b3p6']+':'+source]).decode()
raw=[json.loads(s[len('NEP_RESULT '):]) for s in b.splitlines() if s.startswith('NEP_RESULT ')]
assert len(raw)==292 and all(x['equal'] and set(x['walked_axioms'])<={'propext','Classical.choice','Quot.sound'} for x in raw)
md=(B/'ROWS13.md').read_text();assert len([s for s in md.splitlines() if s.startswith('| V')])==407
ledger=Path('design/PRIVACY-LEDGER-20261026.md').read_text();section=ledger.split('## Recount 13 2026-11-04 (B)')[1]
assert all('Recount '+str(i) in section for i in range(1,14))
table=[s for s in section.splitlines() if s.startswith('|')];assert len({s.count('|') for s in table})==1
assert 'NEW NAMED PREMISE' in section and 'Target not yet established' in section
assert not list(P.rglob('*.lean'))
assert all(p.stat().st_size<20*1024*1024 for p in P.rglob('*') if p.is_file())
diff=subprocess.check_output(['git','diff','--name-only']).decode().splitlines();assert diff==['design/PRIVACY-LEDGER-20261026.md']
result={'status':'PASS','provider_focused_source_hashes_match':4,'b3p6_reused_raw_roots':len(raw),'row_table_entries':407,'totals_columns':'Recount 1 through 13','no_new_proofs':True,'new_runs':{'Lean':0,'Kani':0},'ledger_edit':'append only','target':'Target not yet established'}
(P/'final-check13.json').write_text(json.dumps(result,indent=1)+'\n');print(json.dumps(result))
