#!/usr/bin/env python3
"""Check/install exact source emissions with one shared-instance binder."""
from pathlib import Path
import argparse,hashlib,json
p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args()
tool=Path(__file__).resolve().parent;area=tool.parents[1]
for n in ['Types.lean','Funs.lean']:
 raw=(tool/'canonical-dots-generated'/n).read_bytes();data=raw
 if n=='Funs.lean':
  marker=b'namespace AspisR1CanonicalDots\n';assert raw.count(marker)==1
  data=raw.replace(marker,marker+b'\nvariable [Shared]\n',1)
  assert data.replace(b'\nvariable [Shared]\n',b'',1)==raw
 dest=area/'lean/AspisR1CanonicalDots'/n
 if a.check:assert dest.read_bytes()==data,n
 else:dest.write_bytes(data)
 print(json.dumps(dict(file=n,check=a.check,raw_sha256=hashlib.sha256(raw).hexdigest(),installed_sha256=hashlib.sha256(data).hexdigest())))
