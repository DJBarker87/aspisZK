#!/usr/bin/env python3
"""Inventory source deltas against the immediately previous S10 repin."""
import hashlib,json,subprocess
from pathlib import Path
R=Path(__file__).resolve().parents[2];E=R/'docs/research/100bit-spend-path-20261013/evidence/s10-repin2-20261023'
x=json.loads((E/'source-inputs.json').read_text());old=x['comparison_source_revision']
rows=[]
for r in x['files']:
 if r['changed']:
  d=subprocess.run(['git','diff',old,x['source_revision'],'--',r['path']],cwd=R,text=True,capture_output=True,check=True).stdout
  rows.append(dict(**r,diff=d,classification='test-only wiring' if r['path'].endswith(('lib.rs','adapter_rw_tests.rs')) else 'adapter caller glue (original retained as test-only sibling)' ))
(E/'source-delta.json').write_text(json.dumps(dict(old_revision=old,new_revision=x['source_revision'],changed=rows,unchanged_inputs=len(x['files'])-len(rows)),indent=2)+'\n')
