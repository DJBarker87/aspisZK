"""Add the merged child candidate fold without replaying unchanged raw roots."""
from pathlib import Path
import json,hashlib,re,lzma
E=Path(__file__).resolve().parent;m='NLW_064CandidateFold'
rs=[json.loads(l) for l in (E/'NLW_ATTEMPTS.jsonl').read_text().splitlines()]
h=hashlib.sha256((E/(m+'.lean')).read_bytes()).hexdigest()
good=[r for r in rs if r['kind']=='lean' and r['module']==m and r['exit_status']==0 and h in r['source_hashes'].values()]
assert good
p=E/'NLW_MODULES.json';ms=json.loads(p.read_text());assert m not in ms;ms.append(m);p.write_text(json.dumps(ms,indent=1)+'\n')
p=E/'NLW_SOURCE_SELECTORS.json';s=json.loads(p.read_text());s[m]=good[-1]['attempt'];p.write_text(json.dumps(s,indent=1)+'\n')
p=E/'NLW_AUDIT_ROOTS.json';x=json.loads(p.read_text());old=x['roots'][:];new=[m+'.child',m+'.fold'];x['roots']+=new;x['groups'].append(new);p.write_text(json.dumps(x,indent=1)+'\n')
p=E/'NLW_COMBINED_IMPORT.lean';raw=p.read_text();p.write_text('import '+m+'\n'+raw)
p=E/'NLW_EXPECTED_IMPORTS.jsonl';xs=[json.loads(l) for l in p.read_text().splitlines()]
for r in xs:
 if r['module']=='NLW_COMBINED_IMPORT':r['imports'].insert(1,m)
xs.append(dict(module=m,imports=['Init','NLW_Full064Fold']));p.write_text(''.join(json.dumps(r)+'\n' for r in sorted(xs,key=lambda r:r['module'])))
(E/'NLW_GATE_EXTENSION.json').write_text(json.dumps(dict(reason='Source change: discharge corrected merged NLT child parameter; full native producer still absent',new_module=m,new_roots=new,
 reused_raw_roots=old,reuse_basis='All defining source modules and their selected objects unchanged; import extension introduces one new namespace; final NFX scan validates private closure and import/owner coherence',
 first_combined='NLW_L068',first_scan='NLW_L072',first_raw='NLW_L073..NLW_L080',second_combined='NLW_L082',second_scan='NLW_L083',focused_raw='NLW_L084'),indent=1)+'\n')
for n in ['NLW_LOADED_scan.jsonl.xz','NLW_LOADED_scan.jsonl.sha256']:
 p=E/n;q=E/n.replace('NLW_LOADED_scan','NLW_LOADED_scan_pass1');q.write_bytes(p.read_bytes())
print(json.dumps(dict(modules=len(ms),roots=len(x['roots']),groups=len(x['groups']))))
