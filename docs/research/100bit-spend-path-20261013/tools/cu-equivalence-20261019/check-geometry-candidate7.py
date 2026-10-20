#!/usr/bin/env python3
"""Pinned source, exact library transports, and coherent Candidate7 receipts."""
from pathlib import Path
import argparse,hashlib,json,re,resource,subprocess,sys,time
start=time.monotonic();ap=argparse.ArgumentParser();ap.add_argument('--source-only',action='store_true');a=ap.parse_args()
tool=Path(__file__).resolve().parent;area=tool.parents[1];repo=tool.parents[4];ev=area/'evidence/cu-equivalence-20261019';sha=lambda b:hashlib.sha256(b).hexdigest()
for script in ['extract-geometry-candidate7.py','emit-geometry-candidate7.py','check-wide-arithmetic.py']:
 subprocess.run([sys.executable,str(tool/script),*(['--check']if not script.startswith('check-')else[])],check=True,capture_output=True)
kit=tool/'geometry-candidate7-input';pins=json.loads((kit/'source-pins.json').read_text());production=pins['candidate'];parent=pins['parent']
assert (kit/'field.rs').read_bytes()==(tool/'wide-arithmetic-input/field.rs').read_bytes()
extracted=json.loads((tool/'geometry-candidate7-extraction-pins.json').read_text())
for name,h in extracted['kit_files'].items():assert sha((kit/name).read_bytes())==h,name
for attempt in ['geometry7-charon-d','geometry7-aeneas-d']:
 r=json.loads((ev/attempt/'receipt.json').read_text());assert r['exit_status']==0;assert r['source_pins_sha256']==sha((tool/'geometry-candidate7-extraction-pins.json').read_bytes()),attempt
raw=(tool/'geometry-candidate7-generated/Funs.lean').read_bytes();installed=(area/'lean/AspisR1GeometryCandidate7/Funs.lean').read_bytes()
proof=rb' \(by norm_num \[U32.max,U32.numBits,UScalar.max,UScalarTy.numBits\]; decide\)'
assert re.sub(rb'(toStr "[^"]*")'+proof,rb'\1',installed)==raw
assert b'native_decide'not in installed
modules=['AspisR1GeometryCandidate7/Types','CuSavingsGeometryStd','AspisR1GeometryCandidate7/FunsExternal','AspisR1GeometryCandidate7/Funs','CuSavingsGeometryNode','CuSavingsGeometryRow','CuSavingsGeometryFront','CuSavingsGeometryDispatch','CuSavingsGeometryCaller','CuSavingsGeometryCounter','CuSavingsGeometryCache','CuSavingsGeometryCandidate7']
# The final source-stage wrapper discharges successful-builder and Calls premises.
if (area/'lean/CuSavingsGeometryStage.lean').exists():
 modules.extend(['CuSavingsGeometryStage','CuSavingsGeometrySingle'])
 subprocess.run([sys.executable,str(tool/'check-geometry-callers.py'),'--check'],check=True,capture_output=True)
records={};objects={};allowed={'propext','Classical.choice','Quot.sound','core.fmt.Formatter','Aeneas.Std.core.fmt.Formatter'}
for module in modules:
 p=area/'lean'/(module+'.lean');assert p.exists(),module;source=p.read_bytes();digest=sha(source)
 assert not re.search(rb'(?m)^\s*(?:axiom|constant|opaque)\s|\b(?:sorry|admit|native_decide)\b',source),module
 if a.source_only:continue
 matching=[]
 for path in ev.glob('*/receipt.json'):
  try:r=json.loads(path.read_text())
  except (ValueError,OSError):continue
  if r.get('exit_status')==0 and r.get('source_sha256')==digest and r.get('module','').replace('.','/')==module.replace('.','/'):
   matching.append((path.stat().st_mtime,path,r))
 assert matching,('no successful exact-source receipt',module)
 _,path,r=max(matching,key=lambda t:t[0]);output=r['print_axioms_output'];assert 'sorryAx'not in output and '.decide.ax_'not in output,module
 audits=re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",output);assert audits,module
 for declaration,axioms in audits:assert set(filter(None,re.sub(r'\s+','',axioms).split(',')))<=allowed,(declaration,axioms)
 assert source==(path.parent/'source.lean').read_bytes(),module
 name=module.replace('/','.');objects[name]=r['object_sha256'];records[name]=dict(module=name,attempt=r['attempt'],source_path=str(p.relative_to(repo)),receipt=str(path.relative_to(repo)),receipt_sha256=sha(path.read_bytes()),**{k:r.get(k)for k in ['source_revision','source_sha256','object_sha256','features','command','exit_status','wall_seconds','peak_rss_kib','process_swaps','cgroup_swap_bytes','print_axioms_output','direct_imports','foreign_lean_jobs_at_launch']})
if not a.source_only:
 for module,r in records.items():
  for d in r['direct_imports']:
   if d['module']in objects:assert d['sha256']==objects[d['module']],(module,'incoherent selected import',d)
report=dict(status='SOURCE_AUDIT_PASS'if a.source_only else'CONCRETE_SOURCE_AND_CALLER_CONTEXT_EQUIVALENCE_CHECKED',candidate=production,parent=parent,successes=records,coherent_selected_imports=not a.source_only,source_bindings=pins,source_extraction_pin_sha256=sha((tool/'geometry-candidate7-extraction-pins.json').read_bytes()),source_emission=json.loads((tool/'geometry-candidate7-emission.json').read_text()),measured_stage1_savings_cu=[780,791],measured_settlement_savings_cu=[947,957],production_source_changed=False,protocol_changed=False,axiom_boundary='Standard propext/Classical.choice/Quot.sound plus inherited opaque core.fmt.Formatter TYPE for original checked-index unwrap Debug dictionary; no native-decision, arithmetic-law, cache-lineage or candidate-equivalence axiom.',runtime_evidence='docs/research/100bit-spend-path-20261013/evidence/cu-savings-20261019/FINAL-REPORT.md',audit=dict(command=[sys.executable,*sys.argv],source_revision=subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD'],text=True).strip(),features=[],exit_status=0,wall_seconds=time.monotonic()-start,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss//1024,process_swaps=resource.getrusage(resource.RUSAGE_SELF).ru_nswap,print_axioms='N/A: source/receipt audit; exact Lean axiom outputs retained in successes.'))
caller_audit=ev/'GEOMETRY-CALLER-SOURCE.json'
if caller_audit.exists():
 report['caller_source_bindings']=json.loads(caller_audit.read_text())
 report['caller_source_audit_sha256']=sha(caller_audit.read_bytes())
report['final_theorems']=['AspisR1.CuSavingsGeometryCandidate7.source_query_context','AspisR1.CuSavingsGeometryCandidate7.source_caller_context']
if 'CuSavingsGeometryStage' in records:
 report['final_theorems'].extend(['AspisR1.CuSavingsGeometryStage.source_loop_equivalence','AspisR1.CuSavingsGeometryStage.source_caller_equivalence','AspisR1.CuSavingsGeometrySingle.source_public_query_context'])
if not a.source_only:(ev/'GEOMETRY-CANDIDATE7-FINAL.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(dict(status=report['status'],lean_targets=len(records),candidate_equivalence_axioms=0,coherent_selected_imports=report['coherent_selected_imports'])))
