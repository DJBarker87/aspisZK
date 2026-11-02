from pathlib import Path
import json,re,hashlib
B=Path(__file__).resolve().parent
rows=[];counts={};axioms=set();query_count=0
for p in sorted(B.glob('lean-*/receipt.json')):
 r=json.loads(p.read_text());reports=re.findall(r"'([^']+)' (depends on axioms: \[[^]]*\]|does not depend on any axioms)",(p.parent/'stdout.log').read_text())
 for _,t in reports:
  a=set(t.split('[',1)[1].split(']',1)[0].replace(',',' ').split()) if '[' in t else set();assert a<={'propext','Classical.choice','Quot.sound'};axioms|=a
 row={k:r[k] for k in ['module','attempt','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision']};row['print_axioms_actual']=reports;rows.append(row);counts[str(r['exit_status'])]=counts.get(str(r['exit_status']),0)+1;query_count+=len(reports)
assert len(rows)==78 and counts=={'0':75,'1':2,'134':1},counts
active={r['module'] for r in json.loads((B/'MIGRATION-MANIFEST.json').read_text())['modules']}|{'PV_BR_DiscriminantAdapter','PV_BR_Transport','PV_BR_AdmissionTransport','PV_BR_ByteEncoding'}
valid={json.loads(p.read_text())['module']:json.loads(p.read_text()) for p in sorted(B.glob('lean-*/validation.json'))}
sources={p.stem:p for p in list(B.glob('*.lean'))+list((B/'draft-migration').glob('*.lean'))}
for m in active:assert valid[m]['source_sha256']==hashlib.sha256(sources[m].read_bytes()).hexdigest(),m
(B/'COMPILE-SUMMARY.json').write_text(json.dumps({'lean_attempts':78,'native_attempts':1,'kani_runs':0,'exit_counts':counts,'active_verified_modules':len(active),'active_objects':{m:valid[m] for m in sorted(active)},'actual_print_axioms_reports':query_count,'actual_axioms_union':sorted(axioms),'combined_import_elaborated':False,'full_consumer_elaborated':False,'combined_axioms_audit_run':False,'receipts':rows},indent=2)+'\n')
print('Lean',len(rows),counts,'active verified',len(active),'axioms',sorted(axioms))
