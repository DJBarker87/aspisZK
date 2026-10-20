#!/usr/bin/env python3
"""Compare raw pins and normalize only output path and short-name map ordering."""
from pathlib import Path
import json,hashlib,sys
current,previous=map(Path,sys.argv[1:3]);a=json.loads(current.read_text());b=json.loads(previous.read_text())
r=dict(sha256=hashlib.sha256(current.read_bytes()).hexdigest(),bytes=current.stat().st_size,previous_sha256=hashlib.sha256(previous.read_bytes()).hexdigest(),byte_identical=current.read_bytes()==previous.read_bytes(),has_errors=a['has_errors'])
for x in [a,b]:
 x['translated']['options']['dest_file']='<output>'
 x['translated']['short_names'].sort(key=lambda y:json.dumps(y['key'],sort_keys=True))
r['identical_after_dest_file_and_short_names_order_normalization']=a==b
r['canonical_sha256']=hashlib.sha256(json.dumps(a,sort_keys=True,separators=(',',':')).encode()).hexdigest()
print(json.dumps(r,indent=2))
assert a==b
