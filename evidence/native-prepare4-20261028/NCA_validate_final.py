"""Own final evidence integrity check; no proof launches or shared writes."""
from pathlib import Path
import hashlib,json,re
E=Path(__file__).resolve().parent
lock='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
rows=[]
for cfgp in sorted(list(E.glob('NCA_K[0-9][0-9][0-9].json'))+list(E.glob('NCA_L[0-9][0-9][0-9].json'))):
 a=cfgp.stem;c=json.loads(cfgp.read_text());rp=E/a/'receipt.json'
 if not rp.exists():
  assert a=='NCA_K001',a
  rows.append(dict(attempt=a,kind='kani',launched=False,exit_status=None,wall_seconds=None,peak_rss_kib=None,swaps=None,print_axioms='N/A: no compiler launched',reason='own missing source before snapshot',source_revision=c.get('source_revision')));continue
 r=json.loads(rp.read_text());assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},a
 assert r['swaps']=='0',a
 if c['kind']=='kani':
  g=json.loads((E/(a+'-graph-check.json')).read_text());s=json.loads((E/(a+'-source-check.json')).read_text());k=json.loads((E/(a+'-lock-check.json')).read_text())
  assert g['graph_matches_frozen'] and not g['new_package_tuples'] and not g['edge_errors'] and g['lock_sha256']==lock,a
  assert not s['errors'] and k['unchanged'] and k['before']==k['after']==lock,a
  assert (E/(a+'-lock-after.log')).read_text().split()[0]==lock,a
  p=json.loads((E/(a+'-source-pin.json')).read_text());raw=(E/p['pinset']).read_bytes();assert hashlib.sha256(raw).hexdigest()==p['sha256'] and len(raw)==p['bytes'],a
  out=(E/a/'stdout.log').read_text();r['summary']=re.findall(r'\*\* .*failed[^\n]*|VERIFICATION:[^\n]*|[^\n]*timed out[^\n]*|[^\n]*successfully verified harnesses[^\n]*',out)[-5:]
 else:
  if r['exit_status']==0:
   assert all('sorryAx' not in s and 'axiom' in s for s in r['print_axioms']),a
 rows.append(r)
(E/'NCA_FINAL_ATTEMPTS.json').write_text(json.dumps(rows,indent=2)+'\n')
# Preserve the original append-only ledger; final table is normalized independently.
summary=dict(kani_configured=sum(r['kind']=='kani' for r in rows),lean_configured=sum(r['kind']=='lean' for r in rows),terminal_receipts=len(rows)-1,precompiler_failures=1,source_integrity=True,limits_and_swaps=True)
(E/'NCA_FINAL_VALIDATION.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary))
