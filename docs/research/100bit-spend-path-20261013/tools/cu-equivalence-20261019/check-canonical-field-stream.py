#!/usr/bin/env python3
"""Audit complete field-stream source consumer and coherent focused receipts."""
from pathlib import Path
import argparse,hashlib,json,re,subprocess,sys
ap=argparse.ArgumentParser();ap.add_argument('--source-only',action='store_true');a=ap.parse_args();tool=Path(__file__).resolve().parent;area=tool.parents[1];ev=area/'evidence/cu-equivalence-20261019';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for name in ['extract-canonical-field-stream.py','emit-canonical-field-stream.py']:
 subprocess.run([sys.executable,str(tool/name),'--check'],check=True,stdout=subprocess.DEVNULL)
modules=['AspisR1CanonicalFieldStream/'+part for part in ['Types','FunsExternal','Funs']]+['CuSavingsCanonicalFieldStreamLoop','CuSavingsCanonicalFieldStreamCanonical','CuSavingsCanonicalFieldStream'];records={};rows=[]
for i,mod in enumerate(modules,1):
 p=area/'lean'/f'{mod}.lean';assert not re.search(r'(?m)^\s*(?:axiom|opaque)\s|\bsorry\b|\badmit\b',p.read_text()),mod
 row=dict(module=mod,source_sha256=sha(p))
 if not a.source_only:
  receipt=ev/f'canonical-field-stream-final-{i}/receipt.json';r=json.loads(receipt.read_text());assert r['exit_status']==0 and r['source_sha256']==sha(p),mod
  output=r['print_axioms_output'];assert 'sorryAx' not in output
  audits=re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",output);assert audits,mod
  for name,axs in audits:assert set(filter(None,re.sub(r'\s+','',axs).split(',')))<={'propext','Classical.choice','Quot.sound'},(name,axs)
  records[mod.replace('/','.')]=r
  row.update(receipt=str(receipt),object_sha256=r['object_sha256'])
 rows.append(row)
if not a.source_only:
 for mod,r in records.items():
  for imp in r['direct_imports']:
   if imp['module']in records:assert imp['sha256']==records[imp['module']]['object_sha256'],(mod,imp)
print(json.dumps(dict(status='SOURCE_PASS'if a.source_only else'PASS',targets=len(rows),coherent_selected_imports=not a.source_only,new_axioms=False,complete_original_source_consumer=True)))
