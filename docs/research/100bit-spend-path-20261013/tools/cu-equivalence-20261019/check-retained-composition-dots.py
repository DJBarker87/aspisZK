#!/usr/bin/env python3
from pathlib import Path
import argparse,json,hashlib,re,subprocess,sys
ap=argparse.ArgumentParser();ap.add_argument('--source-only',action='store_true');a=ap.parse_args();tool=Path(__file__).resolve().parent;area=tool.parents[1];ev=area/'evidence/cu-equivalence-20261019';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
subprocess.run([sys.executable,str(tool/'emit-retained-composition-dots.py'),'--check'],check=True,stdout=subprocess.DEVNULL)
selected=json.loads((tool/'retained-composition-dots-selected.json').read_text());selected['CuSavingsRetainedCompositionDots']='retained-composition-dots-final-b';rows=[];objects={};records={}
for mod,attempt in selected.items():
 p=area/'lean'/f'{mod}.lean';text=p.read_text();assert not re.search(r'(?m)^\s*(?:axiom|opaque)\s|\bsorry\b|\badmit\b',text),mod
 row=dict(module=mod,source_sha256=sha(p),declarations=re.findall(r'(?m)^(?:def|theorem|abbrev)\s+([\w.]+)',text))
 if not a.source_only:
  rp=ev/attempt/'receipt.json';r=json.loads(rp.read_text());assert r['exit_status']==0 and r['source_sha256']==sha(p),mod
  audits=re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",r['print_axioms_output']);assert audits,mod
  for decl,axs in audits:assert set(filter(None,re.sub(r'\s+','',axs).split(',')))<={'propext','Classical.choice','Quot.sound','core.fmt.Formatter'},(decl,axs)
  records[mod]=r;objects[mod]=r['object_sha256']
  row.update(receipt=str(rp),**{k:r[k]for k in ['command','source_revision','features','exit_status','wall_seconds','peak_rss_kib','process_swaps','object_sha256','print_axioms_output']})
 rows.append(row)
if not a.source_only:
 for mod,r in records.items():
  for imp in r['direct_imports']:
   if imp['module']in objects:assert imp['sha256']==objects[imp['module']],(mod,imp)
 result=dict(status='PASS',concrete_source_replacements=[4,10],whole_retained_bundle_closed=False,final_theorem='AspisR1.CuSavingsRetainedCompositionDots.all_query_callers',unified_source_namespace='AspisR1RetainedDots',source_admission='Four public field declarations are byte-identical and shared; opaque dot state uses the current source carrier after a checked no-field-inspection audit. New/push/finish remain computational parameters; no propositional API law. Original numeric bodies and source proof closure rechecked on this representation. All nineteen emitted middle-kernel declarations are byte-identical after source module-prefix renaming and used exactly once. Both exact end kernels compose at actual View.query whose source proof derives the prefix bound. Candidate5 source API binding is a separate operation.',coherent_selected_imports=True,selected_targets=rows)
 (ev/'RETAINED-COMPOSITION-DOTS-FINAL.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(status='SOURCE_PASS'if a.source_only else'PASS',targets=len(rows),concrete_replacements=[4,10],whole_retained_bundle_closed=False,coherent_selected_imports=not a.source_only)))
