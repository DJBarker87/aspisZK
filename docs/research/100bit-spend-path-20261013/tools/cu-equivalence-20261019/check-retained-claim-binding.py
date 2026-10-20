#!/usr/bin/env python3
"""Recheck exact source context, fixed imports and kernel-checked receipts."""
from pathlib import Path
import hashlib,json,re,resource,subprocess,sys,time
start=time.monotonic();tool=Path(__file__).resolve().parent;area=tool.parents[1];repo=tool.parents[4];ev=area/'evidence/cu-equivalence-20261019';sha=lambda b:hashlib.sha256(b).hexdigest()
for name in ['extract-retained-claim-binding.py','emit-retained-claim-binding.py','emit-retained-composition-gamma.py']:
 subprocess.run([sys.executable,str(tool/name),'--check'],check=True,capture_output=True)
kit=tool/'retained-claim-binding-input';pins=json.loads((kit/'source-pins.json').read_text());raw=tool/'retained-claim-binding-generated';lean=area/'lean'
assert (raw/'Funs.lean').read_text()==(lean/'AspisR1RetainedClaimBinding/Funs.lean').read_text().replace('\nvariable [DotCall] [Trace]','')
# A value-only nominal transport: exact coordinates and all enum ordinals agree.
rawtypes=(raw/'Types.lean').read_text();shared=(lean/'AspisR1CanonicalDots/Types.lean').read_text()+(lean/'CanonicalVectorTypes.lean').read_text()
for name in ['field.CM31','field.QM31','field.wide_exact.WideExact']:
 pattern=r'structure '+re.escape(name)+r' where\n((?:  [^\n]+\n)+)'
 a=re.search(pattern,rawtypes);b=re.search(pattern,shared);assert a and b and a[1]==b[1],name
assert re.search(r'inductive Error where\n((?:\|[^\n]+\n)+)',rawtypes)[1]in shared
for attempt in ['retained-claim-binding-charon-b','retained-claim-binding-aeneas-b']:
 r=json.loads((ev/attempt/'receipt.json').read_text());assert r['exit_status']==0 and r['source_pins_sha256']==sha((kit/'source-pins.json').read_bytes())
# Complete original source selector, with original field decoder and checked reads.
ctx=re.sub(r'\s+','',(tool/'canonical-vector-context-audit/claim-context.source.rs').read_text())
scalar=re.search(r'letscalar=matchpoint\{(.+?)\};',ctx).group(1)
assert scalar=='0..=2=>sem.claims[point][l],3=>sem.extra[l],4=>sem.before_z1[l],_=>field(y1,l).c0()'
selector=(lean/'CuSavingsRetainedClaimBindingSelector.lean').read_text()
for statement in ['if point.val ≤ 2 then','Array.index_usize sem.claims point','Array.index_usize row l','point = 3#usize','Array.index_usize sem.extra l','point = 4#usize','Array.index_usize sem.before_z1 l','AspisR1CanonicalDots.weights.field y1 l','.ok x.c0']:
 assert statement in selector,statement
modules=['AspisR1RetainedClaimBinding/Types','AspisR1RetainedClaimBinding/FunsExternal','AspisR1RetainedClaimBinding/Funs','CuSavingsRetainedClaimBinding','CuSavingsRetainedClaimBindingPrepared','CuSavingsRetainedClaimBindingSelector','CuSavingsRetainedClaimBindingFinal','CuSavingsRetainedClaimBindingGammaRho']
records={};objects={}
for module in modules:
 p=lean/(module+'.lean');b=p.read_bytes();digest=sha(b)
 assert not re.search(rb'(?m)^\s*(?:axiom|opaque|constant)\s|\b(?:sorry|admit|native_decide)\b',b),module
 matching=[]
 for path in ev.glob('*/receipt.json'):
  try:r=json.loads(path.read_text())
  except(ValueError,OSError):continue
  if r.get('exit_status')==0 and r.get('source_sha256')==digest and r.get('module','').replace('.','/')==module.replace('.','/'):
   matching.append((path.stat().st_mtime,path,r))
 assert matching,('missing exact-source successful receipt',module)
 _,path,r=max(matching,key=lambda x:x[0]);assert (path.parent/'source.lean').read_bytes()==b
 output=r['print_axioms_output'];audits=re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",output);assert audits
 for decl,axioms in audits:assert set(filter(None,re.sub(r'\s+','',axioms).split(',')))<={'propext','Classical.choice','Quot.sound'},(decl,axioms)
 name=module.replace('/','.');objects[name]=r['object_sha256'];records[name]=dict(module=name,attempt=r['attempt'],source_path=str(p.relative_to(repo)),receipt=str(path.relative_to(repo)),receipt_sha256=sha(path.read_bytes()),**{k:r.get(k)for k in ['source_sha256','object_sha256','source_revision','command','features','exit_status','wall_seconds','peak_rss_kib','process_swaps','cgroup_swap_bytes','print_axioms_output','direct_imports']})
for name,r in records.items():
 for imp in r['direct_imports']:
  if imp['module']in objects:assert imp['sha256']==objects[imp['module']],(name,imp)
report=dict(status='FIXED_ACTUAL_CLAIM_PREPARATION_AND_CALLER_CHECKED',candidate=pins['candidate'],successes=records,coherent_selected_imports=True,final_theorems=['AspisR1.CuSavingsRetainedClaimBindingFinal.prepared_equivalence','AspisR1.CuSavingsRetainedClaimBindingFinal.tx1_prepare_equivalence','AspisR1.CuSavingsRetainedClaimBindingGammaRho.source_tx1_equivalence'],source_bindings=pins,selector_source_expression=scalar,selector_source_sha256=sha(selector.encode()),arbitrary_claim_interpretation=False,exported_canonicality_premise=False,exported_child_success_premise=False,exported_candidate_equivalence_premise=False,axioms=['propext','Classical.choice','Quot.sound'],source_context_boundary='Exact inverse-audited helper and counter/context fission; actual checked source outer6+7 loops, actual source arithmetic/powers, exact semantic scalar selector, source-bound original/new dot helpers. Existing unchanged sampler/hash/transcript/observer/semantic-prefix runtime interfaces and Rust/Charon/Aeneas/compiler/library/ownership boundary remain. No whole machine-code proof or new CU measurement.',audit=dict(command=[sys.executable,*sys.argv],source_revision=subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD'],text=True).strip(),features=[],exit_status=0,wall_seconds=time.monotonic()-start,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss//1024,process_swaps=resource.getrusage(resource.RUSAGE_SELF).ru_nswap,print_axioms='N/A: source/receipt audit; all complete Lean outputs retained in successes.'))
(ev/'RETAINED-CLAIM-BINDING-FINAL.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(dict(status=report['status'],lean_targets=len(records),coherent_selected_imports=True,candidate_equivalence_axioms=0)))
