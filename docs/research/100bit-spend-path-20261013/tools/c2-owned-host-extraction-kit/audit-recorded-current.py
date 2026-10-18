#!/usr/bin/env python3
"""Read-only candidate source closure; NO Lean or historical objects loaded."""
import argparse,json,hashlib,re
from pathlib import Path
from collections import defaultdict
sha=lambda b:hashlib.sha256(b).hexdigest()
ap=argparse.ArgumentParser();ap.add_argument('--workspace',type=Path,required=True);ap.add_argument('--git-sources',type=Path,required=True);ap.add_argument('--out',type=Path,required=True);args=ap.parse_args()
C=args.workspace
snap=json.loads((C/'external-inputs.json').read_text());plan=json.loads((C/'preflight-target-plan.json').read_text());G=json.loads(args.git_sources.read_text())
roots=[Path('/home/dombarker/project-offloads')/x/'sources' for x in ['aspis-r1-concrete-decoder-20261013','aspis-line18-import-footprint-20261013','aspis-fs-generic-20261006','aspis-r0-20261006','aspis-r1-mask-lean432-20261015']]
roots.insert(0,Path('/home/dombarker/project-offloads/aspis-r1-mask-lean432-20261015/sources-final-bridge-recheck'))
def imports(t):
 out=[];i=depth=0
 while i<len(t):
  if t[i:i+2]=='/-':depth+=1;i+=2
  elif depth and t[i:i+2]=='-/':depth-=1;i+=2
  elif depth:i+=1
  elif t[i:i+2]=='--':
   j=t.find('\n',i);i=len(t) if j<0 else j
  else:out.append(t[i]);i+=1
 text=''.join(out);deps=[] if re.search(r'^prelude\s*$',text,re.M) else ['Init']
 for line in text.splitlines():
  m=re.fullmatch(r'\s*(?:public |private )?import\s+([\w. ]+)\s*',line)
  if m:deps+=m[1].split()
 return list(dict.fromkeys(deps))
missing={};boundary={};unresolved=[];visiting=set();order=[];paths={}
def visit(m,path):
 if m in missing or m in boundary:return
 if m in visiting:raise Exception(('cycle',m))
 visiting.add(m);paths[m]=path+[m]
 if m in snap['modules'] or m in plan['fresh_topological']:
  n=snap['modules'].get(m, {'current_workspace_target':True});receipt=C/'successful-targets'/(m+'.json')
  boundary[m]={'producer_snapshot':n,'current_rebuild_planned':m in plan['fresh_topological'],'current_receipt_present':receipt.exists()}
  if receipt.exists():boundary[m]['current_receipt']=json.loads(receipt.read_text())
  visiting.remove(m);return
 candidates=[];rel=m.replace('.','/')+'.lean'
 if m in G['modules']:
  n=G['modules'][m];chosen={'path':n['path'],'source_sha256':n['sha256'],'origin':'Git revision '+G['revision'],'source':n['source']}
 else:chosen=None
 for r in roots:
  p=r/rel
  if p.is_file():
   b=p.read_bytes();candidates.append({'path':str(p),'sha256':sha(b)})
   if chosen is None:chosen={'path':str(p),'source_sha256':sha(b),'origin':'Retained host source candidate; needs accepted producer provenance binding','source':b.decode()}
 if chosen is None:
  unresolved.append({'module':m,'import_path':paths[m]});visiting.remove(m);return
 n={**chosen,'imports':imports(chosen['source']),'other_source_candidates':candidates}
 # Mark before recursion to avoid re-walking shared subgraphs.
 missing[m]=n
 for dep in n['imports']:visit(dep,path+[m])
 visiting.remove(m);order.append(m)
visit('C2RecordedExperimentConstruction',[])
out={'classification':'READ_ONLY_AUDIT_NO_LEAN_NO_OBJECT_REUSE','git_revision':G['revision'],'current_base_workspace':str(C),'base_source_manifest_sha256':sha((C/'sources/SOURCE-MANIFEST.json').read_bytes()),'base_sigma_checkpoint_sha256':sha((C/'sigma-checkpoint.json').read_bytes()),'base_scope_status':'PROVISIONAL:168/215 currentC targets complete; producer overlay not final; no RawCut object reused','base_snapshot_sha256':sha((C/'external-inputs.json').read_bytes()),'base_plan_sha256':sha((C/'preflight-target-plan.json').read_bytes()),'entry':'C2RecordedExperimentConstruction','fresh_target_count':len(order),'fresh_topological':order,'fresh_sources':missing,'current_base_boundaries':boundary,'unsupported_imports':unresolved,'example_import_paths':paths,'source_roots':[str(r) for r in roots]}
p=args.out;p.write_text(json.dumps(out,sort_keys=True,indent=2)+'\n')
print(json.dumps({'fresh_targets':len(order),'base_boundaries':len(boundary),'unsupported':unresolved,'topological':order,'sha256':sha(p.read_bytes())},indent=2))
