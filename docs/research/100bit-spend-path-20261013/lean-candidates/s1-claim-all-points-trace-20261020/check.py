#!/usr/bin/env python3
"""Verify all-point source-normalization and loop proof evidence without replay."""
from pathlib import Path
import json,hashlib,re
D=Path(__file__).resolve().parent
P=D.parent.parent
sha=lambda b:hashlib.sha256(b).hexdigest()
manifest=json.loads((D/'manifest.json').read_text())
assert manifest['schema']=='focused-extractor-proof-packet-v1'
assert len(manifest['modules'])==4
for m in manifest['modules']:
 src=(D/m['source']).read_bytes()
 assert sha(src)==m['source_sha256'],m['module']
 assert not re.search(r'\b(sorry|axiom|native_decide)\b|set_option\s+(maxHeartbeats|maxRecDepth)',src.decode()),m['module']
 rec=json.loads((D/m['receipt']).read_text())
 assert rec['exit_status']==0 and rec['scope_swap_peak_bytes']==0,m['module']
 assert rec['source_sha256']==m['source_sha256'] and rec['object_sha256']==m['object_sha256']
 log=(D/m['receipt']).with_name('lean.log').read_text()
 assert 'sorryAx' not in log
 reports=re.findall(r"depends on axioms: \[([^\]]*)\]",log)
 assert reports or 'does not depend on any axioms' in log,m['module']
 for report in reports:
  assert set(re.findall(r'[A-Za-z_.]+',report))<={'propext','Classical.choice','Quot.sound'},report
 pf=json.loads((D/m['receipt']).with_name('preflight.json').read_text())
 for dep,pin in pf['direct_imports'].items():
  assert manifest['direct_import_source_map'][dep]['object_sha256']==pin['sha256'],dep
for line in (D/'SHA256SUMS').read_text().splitlines():
 h,name=line.split('  ',1)
 assert sha((D/name).read_bytes())==h,name
print('PASS: 4 green pinned all-point source/trace targets; standard axioms; exact direct owners; file hashes')
