"""Read the immutable package revision already pinned by the committed J evidence.
No archive is written; compare all eleven recorded exact source hashes first.
"""
from pathlib import Path
import urllib.request,tarfile,io,json,hashlib,subprocess
O=Path(__file__).parent;p='docs/research/100bit-spend-path-20261013/evidence/soundness-env-20261020/retained-comppoly-inventory.json';pin=json.load(open(p));rev=pin['source_revision'];url='https://codeload.github.com/Verified-zkEVM/CompPoly/tar.gz/'+rev
try:
 data=urllib.request.urlopen(url,timeout=30).read()
except Exception as e:
 (O/'EJS_comppoly-package-probe.json').write_text(json.dumps(dict(pin_file=p,revision=rev,url=url,error=str(e)),indent=2)+'\n');print(type(e).__name__,str(e));raise SystemExit(1)
with tarfile.open(fileobj=io.BytesIO(data),mode='r:gz') as t:
 sources={m.name.split('/',1)[1].removesuffix('.lean'):t.extractfile(m).read() for m in t.getmembers() if m.isfile() and '/CompPoly/' in m.name and m.name.endswith('.lean')}
known=json.load(open(O/'EJS_recursive-history-resolution.json'))['found'];compared=[]
for h,r in known.items():
 module=r['path'][r['path'].index('CompPoly/'):].removesuffix('.lean');actual=hashlib.sha256(sources[module]).hexdigest() if module in sources else None;compared.append(dict(module=module,recorded=h,upstream=actual,match=h==actual))
report=dict(pin_file=p,revision=rev,url=url,archive_sha256=hashlib.sha256(data).hexdigest(),archive_bytes=len(data),source_modules=len(sources),comparison=compared,all_match=all(r['match'] for r in compared))
(O/'EJS_comppoly-package-probe.json').write_text(json.dumps(report,indent=2)+'\n');print('package modules',len(sources),'exact cohort matches',sum(r['match'] for r in compared),'/',len(compared))
# Save source text only after the complete attested cohort matches.
if report['all_match']:
 import base64
 (O/'EJS_comppoly-pinned-sources.json').write_text(json.dumps(dict(revision=rev,archive_sha256=report['archive_sha256'],sources={m:dict(source_sha256=hashlib.sha256(b).hexdigest(),source_base64=base64.b64encode(b).decode()) for m,b in sources.items()}))+'\n')
