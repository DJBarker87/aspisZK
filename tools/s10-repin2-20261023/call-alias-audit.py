#!/usr/bin/env python3
"""Distinguish physical call instructions from symbol-alias census records."""
import collections,json
from pathlib import Path
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013/evidence';E=B/'s10-repin2-20261023'
out=[]
for packet in ['s10-repin-20261022','s10-repin2-20261023']:
 for mode,g in json.loads((B/packet/'elf-graphs.json').read_text())['artifacts'].items():
  by=collections.defaultdict(list)
  for c in g['calls']:by[c['address']].append(c)
  for address,rows in by.items():assert all(c==rows[0] for c in rows),address
  out.append(dict(packet=packet,mode=mode,symbol_call_records=len(g['calls']),unique_call_instructions=len(by),symbol_callx_records=g['indirect_calls'],unique_callx_instructions=sum(v[0]['kind']=='indirect' for v in by.values()),duplicate_alias_sites=[dict(address=a,records=len(v),caller=v[0]['caller'],aliases=[s for s in g['symbols'] if s['address']==v[0]['caller']]) for a,v in by.items() if len(v)>1]))
(E/'call-alias-audit.json').write_text(json.dumps(out,indent=2)+'\n');print('alias consistency PASS')
