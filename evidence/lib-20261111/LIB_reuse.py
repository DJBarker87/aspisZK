"""Prefix/import-only reuse of retained deterministic decoder support.
NND_ResultTotal's obsolete AccountCarrier import is replaced by carrier glue;
its outer-map lemma uses the same three-constructor definition locally.
"""
from pathlib import Path
import hashlib,json
E=Path(__file__).resolve().parent;P=E.parent/'model-bridge-20261111'
names=['ResultTotal','V1ValidatorTotal','V1DecoderTotal','V2ValidatorTotal','V2DecoderTotal']
rows=[]
for name in names:
 old='NND_'+name;new='LIB_'+name;p=P/(old+'.lean');raw=p.read_text();s=raw
 for n in names:s=s.replace('NND_'+n,'LIB_'+n)
 if name=='ResultTotal':
  s=s.replace('import NND_AccountCarrier','import LIB_Carriers')
  s=s.replace('NND_Carrier.outer','mapOuter')
  marker='open Aeneas Aeneas.Std Result\n'
  s=s.replace(marker,marker+'def mapOuter {A B : Type} (f : A → B) : Result A → Result B\n | .ok x => .ok (f x)\n | .fail e => .fail e\n | .div => .div\n')
 (E/(new+'.lean')).write_text(s)
 rows.append(dict(source=str(p),source_sha256=hashlib.sha256(raw.encode()).hexdigest(),module=new,sha256=hashlib.sha256(s.encode()).hexdigest(),changes='Prefix/import-only; ResultTotal local mapOuter is same three-constructor definition as NND_Carrier.outer'))
(E/'LIB_REUSE.json').write_text(json.dumps(rows,indent=1)+'\n')
