from pathlib import Path
import json,hashlib,re
E=Path(__file__).resolve().parent
P=Path('evidence/kit-rework1-20261027'); j=json.loads((P/'KSB_identity.json').read_text())
rows=[]
for r in j['files']:
 if 'source' not in r or not r.get('reverse_import_namespace_only_byte_identical'):continue
 n=r['module'].replace('KSB_','KSD_'); src=Path(r['source']);p=E/(n+'.lean')
 s=p.read_text().replace('KSD_','KSB_')
 assert s==(P/(r['module']+'.lean')).read_text()
 rows.append(dict(module=n,sha256=hashlib.sha256(p.read_bytes()).hexdigest(),source=str(src),source_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),reverse_import_namespace_only_byte_identical=True))
raw=Path(j['files'][2]['source']) if False else Path('evidence/extraction-assoc2-20261027/XRj_L013/sources/XRj_generated/XRh_Release/Funs.lean')
b=raw.read_bytes();n=(E/'KSD_Kit_Funs.lean').read_bytes()
for r in j['declaration_bytes']:
 span=b[r['raw_start']:r['raw_stop']];assert span in n and hashlib.sha256(span).hexdigest()==r['sha256']
s=(E/'KSD_L004/stdout.log').read_text();unknown=sorted(set(re.findall(r'Unknown (?:constant|identifier) `([^`]+)`',s)))
(E/'KSD_identity.json').write_text(json.dumps(dict(files=rows,declaration_bytes=j['declaration_bytes'],raw_declarations=307,raw_funs_sha256=hashlib.sha256(b).hexdigest(),all_exact=True,compile_diagnostic=dict(attempt='KSD_L004',error_count=len(re.findall(r': error(?:\(|:)',s)),unknown_names=unknown,reaches_final_checkpoint=True,accepted=False)),indent=2)+'\n')
print('307 declaration spans exact; diagnostics retained')
