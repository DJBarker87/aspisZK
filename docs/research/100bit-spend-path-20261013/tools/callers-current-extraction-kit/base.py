#!/usr/bin/env python3
"""Re-extract every canonical declaration at current accepted lead plus1d/e."""
from pathlib import Path
import argparse,hashlib,importlib.util,json,sys
R=Path(__file__).resolve().parents[5];H=Path(__file__).resolve().parent;T=H.parent;REV='a555c8526'
sha=lambda b:hashlib.sha256(b).hexdigest()
def module(name,path):
 spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');args=ap.parse_args()
prep=module('currentprep',T/'public-preparation-extraction-kit/extract.py');prep.REV=REV
sys.argv=['extract.py','--repo',str(R),'--out',str(H/'preparation')]+(['--check']if args.check else []);prep.main()
layout=(T/'public-preparation-extraction-kit/layout.template.rs').read_bytes();q=H/'preparation/layout.template.rs'
if args.check:assert q.read_bytes()==layout
else:q.write_bytes(layout)
caller=module('currentcaller',T/'digest32-callers-extraction-kit/extract.py');caller.REV=REV;caller.BASE=H/'preparation';out=caller.outputs()
for n,b in out.items():
 p=H/'base52'/n
 if args.check:assert p.read_bytes()==b,n
 else:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
old=json.loads((T/'digest32-callers-extraction-kit/source-pins.json').read_text());new=json.loads(out['source-pins.json']);oldmap={x['name']:x for x in old['cuts']};audit=[]
for cut in new['cuts']:
 prev=oldmap[cut['name']];before=(T/'digest32-callers-extraction-kit/fragments'/(cut['name']+'.rs')).read_text();after=(H/'base52/fragments'/(cut['name']+'.rs')).read_text()
 import difflib
 audit.append({'name':cut['name'],'path':cut['path'],'old_sha256':prev['sha256'],'current_sha256':cut['sha256'],'status':'unchanged'if prev['sha256']==cut['sha256']else're-extracted','statement_diff':''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='accepted-c16',tofile='current-fe80'))})
pins={'revision':new['revision'],'base52_source_pins_sha256':sha(out['source-pins.json']),'old_revision':old['revision'],'declarations':audit,'rule':'All52 source declarations re-located and extracted from current Git blobs; unchanged classification requires full declaration hash. Includes lead begin inline(never) and current serializer amount guard. Enclosing source hashes/byte spans recorded in current pins.'};raw=(json.dumps(pins,indent=2)+'\n').encode();p=H/'base52-refresh-audit.json'
if args.check:assert p.read_bytes()==raw
else:p.write_bytes(raw)
print(json.dumps({'status':'PASS','check':args.check,'current_revision':new['revision'],'current_base52_sha256':sha(out['lib.rs']),'changed':[x['name']for x in audit if x['status']!='unchanged']}))
