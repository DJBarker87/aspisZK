#!/usr/bin/env python3
"""Retain historical strict/alpha distinctions and map to355 actual Names. No CLI."""
import collections,json,pathlib,resource,sqlite3,subprocess,time
from Port31DATA_run import T,E,pin,state,safe
start=time.monotonic();old=json.loads(subprocess.check_output(['git','show','74a62fd7b6:evidence/port29sdkdata-20261025/Port29SDKDATA_Strict-v3-final-audit.json']))
r=next(r for r in old['artifacts'] if r['path'].endswith('comparisons-final.json'));p=safe(r['path']);before=state(p);assert pin(p)==r
x=json.loads(p.read_text());print('historical comparison schema',type(x).__name__,list(x)[:8] if isinstance(x,dict) else len(x))
# Preserve the entire approved historical comparison payload externally by pin;
# retain only the necessary complete smaller original/current differences here.
rows=x if isinstance(x,list) else x.get('comparisons',[])
if not rows and isinstance(x,dict):
 for k,v in x.items():
  if isinstance(v,list) and v and isinstance(v[0],dict):rows+=v
print('row keys',list(rows[0]) if rows else [])
# No inference until exact schema is inspected. This intermediate schema receipt
# is metadata only, deliberately does not claim old/new equality.
result=dict(command=['python3','-B',str(pathlib.Path(__file__))],source=pin(__file__),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),historical_input=pin(p),historical_summary={k:old[k] for k in ['original_current','factor','proof_refreshes']},schema=dict(type=type(x).__name__,keys=list(x) if isinstance(x,dict) else None,row_count=len(rows),row_keys=list(rows[0]) if rows else []),print_axioms='N/A: metadata only',lean_calls=0,pre_post_stat_unchanged=state(p)==before,exit_status=0,wall_seconds=time.monotonic()-start,peak_rss_bytes=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,swaps=resource.getrusage(resource.RUSAGE_SELF).ru_nswap)
(E/'Port31DATA_variants-schema355.json').write_text(json.dumps(result,indent=2)+'\n')
