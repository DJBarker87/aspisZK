from pathlib import Path
import json,re,subprocess,hashlib
P=Path(__file__).parent;rows=json.loads((P/'claim-audit-dispositions.json').read_text());assert len(rows)==57
for r in rows:
 a=r['selected_standard_audit']
 if r['id']=='V270':assert a is None;continue
 assert a and set(a['axioms_normalized'])<={'propext','Classical.choice','Quot.sound'}
 assert any(s.get('exit_status',s.get('lean_exit',s.get('exit')))==0 for s in a['receipt_status'])
assert hashlib.sha256((P/'input-external-object-manifest.json').read_bytes()).hexdigest()=='d9187c800b7479f66ec6147e3c8e91c1158d382c4aa467bf678e76901b9a8c0e'
assert all(f.stat().st_size<20*1024**2 for f in P.rglob('*')if f.is_file())
for f in P.glob('PV_FA_*.lean'):
 assert not re.search(r'^\s*(?:axiom|sorry|admit)\b',f.read_text(),re.M),f
changed=subprocess.check_output(['git','diff','--name-only','505f8745ee','HEAD'],text=True).splitlines();assert all(x.startswith('evidence/pv-fmtaudit-20261029/')for x in changed)
receipts=[]
for f in(P/'host').glob('*/receipt/receipt.json'):
 r=json.loads(f.read_text());receipts.append(dict(path=str(f.relative_to(P)),attempt=r.get('attempt'),kind=r.get('kind'),exit=r.get('exit_status'),wall=r.get('wall_seconds'),peak_rss_kib=r.get('peak_rss_kib'),swaps=r.get('swaps'),source_revision=r.get('source_revision'),source_sha256=r.get('source_sha256'),command=r.get('command'),print_axioms=r.get('print_axioms')))
lean=[r for r in receipts if r['kind']in ['lean','pincompile']];native=[r for r in receipts if r['kind']not in ['lean','pincompile']];assert len(lean)<=60;assert len(native)<=10
(P/'receipt-index.json').write_text(json.dumps(dict(Lean=len(lean),native=len(native),Kani=0,receipts=sorted(receipts,key=lambda x:x['attempt']or 0)),indent=1))
print(json.dumps(dict(credited_rows=57,selected_standard_theorem_receipts=56,Lean=len(lean),native=len(native),Kani=0,changed_paths_within_job=True,large_files=False)))
