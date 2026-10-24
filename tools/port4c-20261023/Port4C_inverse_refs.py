#!/usr/bin/env python3
"""Namespace-only replay of missing retained inverse objects in private modules."""
from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parents[2];L=R/'docs/research/100bit-spend-path-20261013/lean';E=R/'evidence/port4c-20261023'
mapping={'S7JoinInverseBackend':'Port4C_InverseBackend','S7JoinBatchInverse':'Port4C_BatchInverse','S7JoinInverseExecution':'Port4C_InverseExecution','S7JoinGeometryInversion':'Port4C_OwnedGeometryInverse','S7Kani3InverseLoop':'Port4C_OwnedInverse'}
rows=[]
for old,new in mapping.items():
 s=(L/(old+'.lean')).read_text();original=s
 if old=='S7JoinBatchInverse':s=s.replace('import S7Kani3GeometryStorage','import Port4C_OwnedInverse')
 for a,b in mapping.items():s=s.replace(a,b)
 if old=='S7Kani3InverseLoop':s=s.replace('namespace Port4C_OwnedInverse','namespace AspisR1.Port4C_OwnedInverse').replace('end Port4C_OwnedInverse','end AspisR1.Port4C_OwnedInverse')
 s='-- Private namespace replay of retained mathematical inverse reference; no native-source adoption.\n'+s
 if old=='S7Kani3InverseLoop':continue # Existing accepted namespace replay is already pinned.
 (L/(new+'.lean')).write_text(s)
 rows.append({'retained_source':old,'retained_sha256':hashlib.sha256(original.encode()).hexdigest(),'private_module':new,'private_sha256':hashlib.sha256(s.encode()).hexdigest(),'changes':'Namespace/import replacement only; unused GeometryStorage import replaced by the exact backward recurrence actually used'})
(E/'inverse-reference-replays.json').write_text(json.dumps(rows,indent=2)+'\n')
