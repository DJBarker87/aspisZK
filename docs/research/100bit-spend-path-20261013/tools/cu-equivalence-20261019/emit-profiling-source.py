#!/usr/bin/env python3
"""Invertible generated Phase registration qualification; Funs unchanged."""
from pathlib import Path
import argparse,json,hashlib
from qualify_discriminants import qualify
p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args();tool=Path(__file__).resolve().parent;area=tool.parents[1];sha=lambda b:hashlib.sha256(b).hexdigest()
for name in ['Types.lean','Funs.lean']:
 raw=(tool/'profiling-marker-generated'/name).read_bytes();data=qualify(raw,'AspisR1Profiling') if name=='Types.lean'else raw;dest=area/'lean/AspisR1Profiling'/name
 if a.check:assert dest.read_bytes()==data,name
 else:dest.write_bytes(data)
 print(json.dumps(dict(file=name,check=a.check,raw_sha256=sha(raw),promoted_sha256=sha(data),registration_only=name=='Types.lean')))
