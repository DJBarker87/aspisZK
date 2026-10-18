#!/usr/bin/env python3
"""Coherent exact project reverse closure plus current package objects only."""
from pathlib import Path
import json,importlib.util,re,shutil,time
P=Path('/home/dombarker/project-offloads/aspis-r1-worker-c-paired-current-20261017');O=Path('/home/dombarker/project-offloads/aspis-r1-j17-port-20261015/bridge');W=Path('/home/dombarker/project-offloads/aspis-r1-worker-c-selected-current-20261017');W.mkdir(exist_ok=True);shutil.copy2(P/'runner.py',W/'runner.py');sp=importlib.util.spec_from_file_location('r',W/'runner.py');r=importlib.util.module_from_spec(sp);sp.loader.exec_module(r);D=json.loads((P/'external-inputs.json').read_text());M=json.loads((P/'sources/SOURCE-MANIFEST.json').read_text());sha=r.sha
D['roots'].append({'name':'paired_current','source':str(P/'sources'),'objects':str(P/'objects')})
for n in M['topological_order']:
 src=P/'sources'/(r.stem(n)+'.lean');rp=P/'successful-targets'/(n+'.json');rc=json.loads(rp.read_text());ob=r.object_pins(P/'objects',n,D['olean_header_seal']);assert rc['exit_status']==0 and rc['axioms']['passed'] and rc['key']['source_sha256']==sha(src) and rc['objects']==ob
 for dep,di in rc['key']['imports'].items():assert D['modules'][dep]['objects']==di['objects'],(n,dep)
 D['modules'][n]={'root':'paired_current','source':str(src),'source_sha256':sha(src),'imports':r.imports(src,True),'objects':ob,'build_receipt':{'path':str(rp),'sha256':sha(rp)}};D['provenance_files'][str(rp)]=sha(rp)
G={};order=[]
def visit(n):
 if n in G:return
 if n in D['modules']:
  G[n]={'source':D['modules'][n]['source'],'imports':D['modules'][n]['imports'],'kind':'current'};return
 split=W/'split-sources'/(r.stem(n)+'.lean');old=O/'sources'/(r.stem(n)+'.lean')
 if split.exists():p=split;kind='fresh'
 elif old.exists():p=old;kind='fresh'
 else:
  found=[(root,Path(root['source'])/(r.stem(n)+'.lean')) for root in D['roots'] if (Path(root['source'])/(r.stem(n)+'.lean')).exists()];assert found,('missing source',n);root,p=found[0];assert root['name'] in {'mathlib','plausible','LeanSearchClient','importGraph','proofwidgets','aesop','Qq','batteries','Cli','runtime','runtime_lake'},('Unproved non-package object reuse',n,root['name']);kind='current_package'
 deps=r.imports(p,True);G[n]={'source':str(p),'imports':deps,'kind':kind};
 for dep in deps:visit(dep)
 order.append(n)
 if kind=='current_package':
  ob=r.object_pins(root['objects'],n,D['olean_header_seal']);D['modules'][n]={'root':root['name'],'source':str(p),'source_sha256':sha(p),'imports':deps,'objects':ob}
# New minimal generic declaration module first; sigma core has unchanged fresh
# prerequisites and must be compiled after those exact prerequisites.
for n in ['R1UnifiedSamplerPublic','R1SelectedChallengeMapCore','R1SemanticPrefixCompletedAgreement']:visit(n)
mods={};review=[]
for n in order:
 v=G[n]
 if v['kind']!='fresh':continue
 src=Path(v['source']);body=src.read_text();dest=W/'sources'/(r.stem(n)+'.lean');dest.parent.mkdir(parents=True,exist_ok=True);dest.write_text(body)
 mods[n]={'stage_as':r.stem(n)+'.lean','source_sha256':sha(dest),'imports':r.imports(dest),'source_revision':'a555 production frozen; proof-only Public/sigma declaration import split over exact historical sources refreshed onto current repaired dependencies','source':str(src),'role':('Exact current reverse closure; displayed #print axioms exports audited' if re.search(r'^\s*#print\s+axioms\s+',r.uncomment(body),re.M) else 'Compile-only exact-source prerequisite; zero exported theorem claims; final consuming bridge axioms audit covers use'),'axiom_requests':len(re.findall(r'^\s*#print\s+axioms\s+',r.uncomment(body),re.M))}
 review.append({'module':n,'lines':len(body.splitlines()),'bytes':len(body.encode()),'native_decide_occurrences':len(re.findall(r'\bnative_decide\b',r.uncomment(body))),'recurrence_or_certificate_name':bool(re.search(r'(?i)certificate|generated|elimination|recurrence',n)),'long_numeric_literals':sorted(set(re.findall(r'(?<![A-Za-z0-9_])\d{13,}(?![A-Za-z0-9_])',body)))[:25],'broad_reducer_lines':[{'line':i,'text':line.strip()[:250]} for i,line in enumerate(body.splitlines(),1) if re.search(r'\bnorm_num\b|\bdecide\b|\brfl\b',line) and(re.search(r'\d{10}',line) or 'native_decide' in line)]})
fresh=[n for n in order if n in mods];packages=[n for n in order if G[n]['kind']=='current_package'];assert len(fresh)<240 and len(packages)<200
r.dump(W/'preflight-target-plan.json',{'created_utc':time.time(),'fresh_topological':fresh,'current_package_additions':packages,'fresh_count':len(fresh),'package_count':len(packages),'old_project_objects_reused':0,'caps':{'MemoryHigh':'6G','MemoryMax':'8G','MemorySwapMax':0},'exclusive_lean':True,'review_point':'stop at600seconds without a newly compiled target or memory cap; inspect failures before any retry; no cap increase','stages':{'first5':fresh[:5],'remaining':fresh[5:]},'source_shape_review':review,'rule':'Fresh exact current source proof reverse closure; not a frozen whole-manifest replay. No source constructor/arithmetic change; public and sigma moves preserve qualified names and exact bodies.'})
D['provenance_files'][str(W/'proof-import-split-audit.json')]=sha(W/'proof-import-split-audit.json');r.dump(W/'external-inputs.json',D);r.dump(W/'sources/SOURCE-MANIFEST.json',{'format':2,'modules':mods,'topological_order':fresh,'groups':{'first5':fresh[:5],'complete-hread':fresh}});print(json.dumps({'fresh_count':len(fresh),'package_additions':len(packages),'old_project_objects_reused':0,'first5':fresh[:5],'shape_flags':[v for v in review if v['recurrence_or_certificate_name'] or v['native_decide_occurrences'] or v['long_numeric_literals'] or v['broad_reducer_lines']]}))
