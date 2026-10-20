#!/usr/bin/env python3
"""Check concrete chronological4/5/10 source composition and focused receipts."""
from pathlib import Path
import argparse,hashlib,json,re,subprocess,sys
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args();tool=Path(__file__).resolve().parent;area=tool.parents[1];repo=tool.parents[4];ev=area/'evidence/cu-equivalence-20261019';sha=lambda b:hashlib.sha256(b).hexdigest()
for script,args in [('check-retained-composition-dots.py',[]),('check-retained-input-bindings.py',['--check']),('check-dots-retained-composition.py',['--check'])]:
 subprocess.run([sys.executable,str(tool/script),*args],check=True,stdout=subprocess.DEVNULL)
names=['retained-dots-binding-a','retained-dots-tail-d','retained-dots-suffix-g','retained-dots-middle-c','retained-dots-kernel-a','retained-dots-inputs-b','retained-dots-representation-b','retained-dots-resumed-b','retained-resume-dot-binding-b','retained-resume-dots-context-c','retained-fresh-dots-context-a']
selected={};rows=[]
for name in names:
 rp=ev/name/'receipt.json';r=json.loads(rp.read_text());p=area/'lean'/(r['module']+'.lean');text=p.read_text()
 assert r['exit_status']==0 and r['source_sha256']==sha(p.read_bytes()),name
 assert r['process_swaps']==r['cgroup_swap_bytes']==0,name
 assert not re.search(r'(?m)^\s*(?:axiom|opaque)\s|\bsorry\b|\badmit\b',text),name
 axs=re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",r['print_axioms_output']);assert axs,name
 for decl,used in axs:assert set(filter(None,re.sub(r'\s+','',used).split(',')))<={'propext','Classical.choice','Quot.sound','core.fmt.Formatter'},(name,decl,used)
 selected[r['module']]=r['object_sha256']
 rows.append(dict(module=r['module'],attempt=name,source_path=str(p.relative_to(repo)),receipt_path=str(rp.relative_to(repo)),source_sha256=r['source_sha256'],object_sha256=r['object_sha256'],receipt_sha256=sha(rp.read_bytes()),declarations=re.findall(r'(?m)^(?:def|theorem|abbrev)\s+([\w.]+)',text),**{k:r[k]for k in ['command','source_revision','features','exit_status','wall_seconds','peak_rss_kib','process_swaps','cgroup_swap_bytes','print_axioms_output','direct_imports']}))
for report,key in [('RETAINED-COMPOSITION-DOTS-FINAL.json','selected_targets'),('RETAINED-INPUT-BINDINGS-FINAL.json','selected')]:
 for row in json.loads((ev/report).read_text())[key]:selected[row['module'].replace('/','.')]=row['object_sha256']
for row in rows:
 for imp in row['direct_imports']:
  if imp['module']in selected:assert imp['sha256']==selected[imp['module']],(row['module'],imp['module'])
# Definitional source factors are deliberately explicit, not candidate-equality hypotheses.
for module,theorem in [('Suffix','source_factor'),('Middle','source_factor')]:
 text=(area/'lean'/('CuSavingsRetainedDots'+module+'.lean')).read_text();assert 'theorem '+theorem in text
representation=(area/'lean/CuSavingsRetainedDotsRepresentation.lean').read_text();assert 'push_counts' in representation and 'old_recover' in representation
report=dict(status='PASS',frozen='39c2971dd16c95858a4cfd2c9ae35da052eacfa9',concrete_source_replacements=[4,5,10],closed_dot_kernel_composition=True,whole_retained_bundle_closed=False,selected=rows,coherent_selected_imports=True,source_boundaries=['Existing byte-pinned chronological old/middle/new numeric source contexts, audited nineteen identical common middle declarations and zero dot-field-inspection source abstraction.','Concrete candidate5 original/new API wrappers use coordinate copies only; erased original privatecounts reconstruct exactly at initialization and every successful original push.','Exact source suffix/prefix factors are kernel-checked; unchanged add/fromLimbs computations shared without algebraic laws.','Actual gamma source powers are canonical by checked sampler/strict-reader/powers arithmetic; no canonicality premise on fresh_source_equivalence.'],endpoints=['CuSavingsRetainedDotsInputs.fresh_source_equivalence','CuSavingsRetainedDotsResumed.reader_powers_query','CuSavingsRetainedResumeDotBinding.query_equivalence','CuSavingsRetainedFreshDotsContext.source_equivalence','CuSavingsRetainedResumeDotsContext.source_equivalence'],fresh_scope='FreshDotsContext.source_equivalence executes complete actual tx1_prepare under actual scalar/powers computational binding and then actual View.query; it derives origins internally on success and preserves fail/div/Err including returned scratch state. No success/canonicality premise. This is explicit preparation/query source-fission context, not yet the specialized QueryCommon.queryPrefix runtime.',resumed_scope='Actual Reader.e success and actual powers success imply complete query callback equivalence. ResumeDotBinding computationally specializes actual TxCommon.powers and consumes source ReaderOrigin without a canonicality premise. ResumeDotsContext.source_equivalence executes actual complete resume, actual powers and actual View.query without a success/canonicality premise, using source_inputs to derive origins internally. The outer source prefix-to-suffix factor is explicit; specializing whole stage QueryCommon.queryPrefix remains a separate integration task, and no complete tx2/auth closure is claimed.',runtime_boundary='Existing audited Rust→Charon→Aeneas source/runtime boundary, coordinate-only public carriers and source-parametric private ADT representation with checked recovery. Formatter is inherited unchanged debug unwrap runtime type, not an equivalence law.',repin_inventory='Production sources unchanged; no newly changed Rust function to repin. Existing candidate4/5/10 Digest32 repin inventories remain applicable. New Lean source declarations listed in selected records.')
b=(json.dumps(report,indent=2)+'\n').encode();p=ev/'RETAINED-DOTS-CANONICAL-COMPOSITION-FINAL.json'
if a.check:assert p.read_bytes()==b
else:p.write_bytes(b)
print(json.dumps(dict(status='PASS',check=a.check,selected=len(rows),combined=[4,5,10],max_rss_kib=max(r['peak_rss_kib']for r in rows),coherent_selected_imports=True)))
