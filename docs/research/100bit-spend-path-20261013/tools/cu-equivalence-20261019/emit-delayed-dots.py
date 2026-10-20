#!/usr/bin/env python3
"""Check/install candidate-4 exact emitted bodies with one shared instance binder."""
from pathlib import Path
import argparse,hashlib,json
p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args()
tool=Path(__file__).resolve().parent;area=tool.parents[1];sha=lambda b:hashlib.sha256(b).hexdigest()
raw=(tool/'delayed-dots-generated/Funs.lean').read_bytes()
marker=b'namespace AspisR1DelayedDots\n';assert raw.count(marker)==1
out=raw.replace(marker,marker+b'\nvariable [Shared]\n',1)
assert out.replace(b'\nvariable [Shared]\n',b'',1)==raw
for n,data in [('Funs.lean',out),('Types.lean',(tool/'delayed-dots-generated/Types.lean').read_bytes())]:
 dest=area/'lean/AspisR1DelayedDots'/n
 if a.check:assert dest.read_bytes()==data,n
 else:dest.write_bytes(data)
print(json.dumps(dict(check=a.check,raw_funs_sha256=sha(raw),installed_funs_sha256=sha(out),changes=['One namespace instance variable; all emitted declaration bodies byte-identical.'])))
