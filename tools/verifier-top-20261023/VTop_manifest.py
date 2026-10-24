#!/usr/bin/env python3
"""Audit receipts and final new-source coverage without replaying a prover."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/verifier-top-20261023';L=R/'docs/research/100bit-spend-path-20261013/lean'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();allow={'propext','Classical.choice','Quot.sound'};rows=[];accepted=[]
for p in sorted(E.glob('*/receipt.json')):
 x=json.loads(p.read_text());assert x['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 for f,h in x['source_hashes'].items():assert sha(p.parent/'sources'/f)==h,(p,f)
 standard=True
 superseded=x['attempt'] in {'lean-020','lean-028','lean-034','lean-035','lean-037'}
 if x['kind']=='lean':
  for line in x['print_axioms']:
   m=re.search(r'axioms: \[([^\]]*)\]',line)
   if m and not {a.strip() for a in m[1].split(',')}<=allow:standard=False
  if x['exit_status']==0 and standard and not superseded:accepted.append(x)
 rows.append({'attempt':x['attempt'],'kind':x['kind'],'target':x['sources'],'source_revision':x['source_revision'],'exit':x['exit_status'],'wall_seconds':x['wall_seconds'],'peak_rss_kib':int(x['peak_rss_kib']),'swaps':int(x['swaps']),'source_hashes':x['source_hashes'],'standard_axioms_only':standard if x['kind']=='lean' else None,'superseded_interface':superseded,'accepted_for_final':x['kind']=='lean' and x['exit_status']==0 and standard and not superseded,'print_axioms':x['print_axioms'],'receipt':str(p.relative_to(R))})
coverage={}
for p in sorted(L.glob('VTop_*.lean')):
 s=p.read_text();assert not re.search(r'\b(sorry|axiom|admit|native_decide)\b|set_option\s+(maxHeartbeats|maxRecDepth)',re.sub(r'/\-.*?\-/|--[^\n]*','',s,flags=re.S)),p
 covered=[x for x in accepted if x['source_hashes'].get(p.name)==sha(p)];assert covered,p
 coverage[p.name]={'sha256':sha(p),'accepted_attempt':covered[-1]['attempt']}
initial=json.loads((E/'target.json').read_text());assert all(sha(R/p)==x['sha256'] for p,x in initial['files'].items())
compiles=sum(r['kind']=='lean' for r in rows);assert compiles<=100
audit=next(x for x in reversed(accepted) if x['sources']==['VTop_ContinuationAudit.lean'] and x['source_hashes']['VTop_ContinuationAudit.lean']==sha(L/'VTop_ContinuationAudit.lean'))
out={'schema':'focused-extractor-proof-packet-v1','status':'partial: extracted stage identities, typed call order, conditional checkpoint composition and named typed oracle substitution; concrete source/model interpretation and frozen2 accepted-run join remain open','lean_compile_attempts':compiles,'lean_reserved_attempt_ids':len(list((R/'tools/verifier-top-20261023').glob('lean-*.json'))),'kani_runs':0,'preflight_only':['lean-010'],'attempts':rows,'final_sources':coverage,'final_audit':audit['attempt'],'frozen_source_pins_unchanged':True,'max_peak_rss_kib':max(r['peak_rss_kib'] for r in rows),'total_swaps':sum(r['swaps'] for r in rows),'source_revision_at_audit':audit['source_revision'],'qualification':'Focused cached dependency reuse, not a coherent H5 release rebuild. Generated templates and failed/nonstandard audits excluded.'}
(E/'manifest.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:out[k] for k in ['lean_compile_attempts','kani_runs','final_audit','max_peak_rss_kib','total_swaps']},indent=2))
