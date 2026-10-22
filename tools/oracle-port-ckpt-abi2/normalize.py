#!/usr/bin/env python3
"""Reproduce the recorded, syntax-only adaptations of the new extraction."""
from pathlib import Path
import hashlib,json,re,sys
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/ckpt-abi2-20261021'
rows=json.loads((E/'extraction-normalization.json').read_text())
for name in ['Types','Funs']:
 raw=(E/'host/extraction'/(name+'.lean.txt')).read_bytes();s=raw.decode()
 entry=next(r for r in rows if r['path'].endswith('/'+name+'.lean'))
 assert hashlib.sha256(raw).hexdigest()==entry['emitted_sha256']
 s=re.sub(r'^set_option max(?:Heartbeats|RecDepth) \d+\n','',s,flags=re.M)
 if name=='Types':
  assert s.count('aspis_r1_cost_probe.transport.Variant')==5
  s=s.replace('aspis_r1_cost_probe.transport.Variant','aspis_r1_cost_probe.transport.CheckpointAbi2Variant')
 else:
  s+='\n#print axioms OraclePortCkptAbi2Extracted.body_byte\n#print axioms OraclePortCkptAbi2Extracted.decode_k_spec\n#print axioms OraclePortCkptAbi2Extracted.decode_e_spec\n'
 assert hashlib.sha256(s.encode()).hexdigest()==entry['normalized_sha256']
 p=B/'lean/OraclePortCkptAbi2Extracted'/(name+'.lean')
 if '--check' in sys.argv:assert p.read_text()==s
 else:p.write_text(s)
print('Exact extraction normalization and definition audits match')
