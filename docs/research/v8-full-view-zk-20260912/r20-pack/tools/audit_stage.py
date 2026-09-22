#!/usr/bin/env python3
"""Read-only manifest and call-site inventory. No network or source modification."""
import argparse,hashlib,json,pathlib
p=argparse.ArgumentParser();p.add_argument('stage',type=pathlib.Path);a=p.parse_args();root=a.stage.resolve()
m=json.loads((root/'r18-stage.json').read_text())
if m.get('profile')!='AV8/R19/sparseG-T163/quadratic-channel-fold/research-v1':raise SystemExit('wrong source profile')
checked=0
for n,h in m.get('files',{}).items():
    f=(root/n).resolve()
    if root not in f.parents:raise SystemExit('path escapes stage')
    if not f.is_file() or hashlib.sha256(f.read_bytes()).hexdigest()!=h:raise SystemExit('source pin failed: '+n)
    checked+=1
ex=root/'docs/research/v8-no-work-100-20260907/experiments'
need={
'r17_host_relation.rs':['opened_channel','r19_channel_ordinary','r18_compact_g'],
'query_arithmetic.rs':['fn gamma','decode','helpers'],
'r19_channel_ordinary.rs':['terminal','prepare_rows'],
'r18_compact_g.rs':['coin_weights_into','geometry'],
'performance_verifier.rs':['semantic','payment_terminal']}
report={}
for n,words in need.items():
    f=ex/n
    if not f.is_file():raise SystemExit('missing assembled source '+n)
    s=f.read_text();report[n]={'sha256':hashlib.sha256(f.read_bytes()).hexdigest(),
       'matches':{w:[i+1 for i,l in enumerate(s.splitlines()) if w in l] for w in words}}
print(json.dumps({'checked_files':checked,'profile':m['profile'],'sites':report,
 'flags_are_not_call_graph_evidence':True,'compiler_emission_not_audited':True},indent=2))
