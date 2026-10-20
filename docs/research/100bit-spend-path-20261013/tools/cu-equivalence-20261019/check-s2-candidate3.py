#!/usr/bin/env python3
"""Audit exact source emissions, accepted proof closure and unchanged callers."""
from pathlib import Path
import hashlib,json,re,resource,subprocess,sys,time
started=time.monotonic();tool=Path(__file__).resolve().parent;area=tool.parents[1];repo=tool.parents[4];ev=area/'evidence/cu-equivalence-20261019';sha=lambda b:hashlib.sha256(b).hexdigest()
git=lambda *a:subprocess.check_output(['git','-C',str(repo),*a])
candidate='d631a90ec0b75d2efbeaf62b7ee9c1ba9aac7ffe';parent='ad5bf503319b90d152baaa1dfb5c037d278eb4bd';frozen='39c2971dd16c95858a4cfd2c9ae35da052eacfa9'
assert git('rev-parse',candidate+'^').decode().strip()==parent
for name in ['extract-s2-groups.py','emit-s2-groups.py']:
 subprocess.run([sys.executable,str(tool/name),'--check'],check=True,capture_output=True)
assert git('diff','--name-only',parent,candidate).decode().splitlines()==['crates/aspis-r1-cost-probe/src/weights.rs']
assert git('diff',frozen,'--','crates','programs')==b''
kit=tool/'s2-groups-input';pins=json.loads((kit/'source-pins.json').read_text())
assert pins['candidate']==candidate and pins['parent']==parent
for name,h in pins['kit_files'].items():assert sha((kit/name).read_bytes())==h,name
for p in pins['fragments']:
 data=git('show',p['revision']+':'+p['path']);assert sha(data)==p['file_sha256']
 assert sha(data[p['start_byte']:p['end_byte_exclusive']])==p['fragment_sha256']
for attempt in ['s2-groups-charon-b','s2-groups-aeneas-b']:
 r=json.loads((ev/attempt/'receipt.json').read_text());assert r['exit_status']==0
 assert r['source_pins_sha256']==sha((kit/'source-pins.json').read_bytes())
# Raw output and producing binaries are verified against the selected host output.
provenance=json.loads((tool/'s2-emission-provenance.json').read_text())
for name in ['Funs.lean','Types.lean']:
 assert provenance['hashes'][name]==sha((tool/'s2-groups-generated'/name).read_bytes())
path='crates/aspis-r1-cost-probe/src/weights.rs'
def item(data,name):
 m=re.search(rb'\bfn '+name.encode()+rb'(?:\s*\(|<)',data);assert m,name
 begin=m.start();op=data.index(b'{',m.end());end=op+1;depth=1
 while depth:depth+=(data[end:end+1]==b'{')-(data[end:end+1]==b'}');end+=1
 return begin,end,data[begin:end]
cur=git('show',candidate+':'+path);old=git('show',parent+':'+path);prod=git('show',frozen+':'+path)
for name in ['grouped_inactive_pair','s2_grouped_inactive_pair','raw','field']:
 assert item(cur,name)[2]==item(prod,name)[2],name
for name in ['raw','field']:
 assert item(cur,name)[2]==item(old,name)[2],name
for name in [b'S2_INACTIVE_GROUPS',b'S2_INACTIVE_MASKS']:
 pattern=rb'const '+name+rb'[^=]*=([^;]*);'
 assert re.search(pattern,cur).group(0)==re.search(pattern,prod).group(0)
# Exact unchanged source consumers; the checked theorem permits any computational
# context. These are syntactic bindings, not separately extracted entrypoints.
contexts={};dest=tool/'s2-source-contexts';dest.mkdir(exist_ok=True)
for name,source_path in [('pair',path),('finish_relation','crates/aspis-r1-cost-probe/src/verifier.rs')]:
 source=git('show',candidate+':'+source_path);previous=git('show',parent+':'+source_path)
 a,b,data=item(source,name);assert data==item(previous,name)[2]
 (dest/(name+'.rs')).write_bytes(data)
 contexts[name]=dict(source_path=source_path,start_byte=a,end_byte_exclusive=b,file_sha256=sha(source),source_text_sha256=sha(data),kind='Unchanged source context; universal extensional substitution, no separate transaction extraction claimed.')
assert item(cur,'pair')[2].count(b'grouped_inactive_pair(')==1
assert b'.pair(' in (dest/'finish_relation.rs').read_bytes()
selected={
'AspisR1S2Groups/Types':'s2-source-types-a','AspisR1S2Groups/FunsExternal':'s2-source-externals-b','AspisR1S2Groups/Funs':'s2-source-funs-c',
'CuSavingsS2SourceCommon':'s2-source-common-b','CuSavingsS2SourceControl':'s2-control-e','CuSavingsS2SourceRowDigit':'s2-row-digit-b','CuSavingsS2SourceRow':'s2-row-b',
'CuSavingsS2SourceTables':'s2-source-tables-a','CuSavingsS2SourceInactive':'s2-inactive-c','CuSavingsS2MaskBits':'s2-mask-bits-b','CuSavingsS2SourceSearch':'s2-search-b',
'CuSavingsS2SourceMaskFlag':'s2-mask-flag-a','CuSavingsS2SourceMask':'s2-mask-b','CuSavingsS2SourceArrays':'s2-arrays-b','CuSavingsS2SourceCatalog':'s2-catalog-d',
'CuSavingsS2SourceCoefficientStep':'s2-coefficient-step-b','CuSavingsS2SourceCoefficientLoop':'s2-coefficient-loop-b','CuSavingsS2SourceTailStep':'s2-tail-step-a','CuSavingsS2SourceTail':'s2-tail-a','CuSavingsS2SourceKernel':'s2-kernel-b','CuSavingsS2Candidate3':'s2-candidate3-d'}
objects={};receipts={};results={}
allowed={'propext','Classical.choice','Quot.sound','core.fmt.Formatter','Aeneas.Std.core.fmt.Formatter'}
for module,attempt in selected.items():
 rp=ev/attempt/'receipt.json';r=json.loads(rp.read_text());src=(area/'lean'/(module+'.lean')).read_bytes()
 assert r['exit_status']==0 and sha(src)==r['source_sha256'] and src==(ev/attempt/'source.lean').read_bytes(),module
 assert not re.search(rb'(?m)^\s*(?:axiom|constant)\s|\b(?:sorry|admit)\b',src),module
 output=r['print_axioms_output'];assert 'sorryAx' not in output and 'error:' not in output
 decls=re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",output);assert decls,module
 for name,axs in decls:assert set(filter(None,re.sub(r'\s+','',axs).split(',')))<=allowed,(name,axs)
 assert r['cache_provenance']['selected_owner_objects']['Aeneas']['sha256']=='d3bfce818c2409992274bc1852aa00280cb7a8139465ef0bab674498e4cdc69d'
 assert not r['foreign_lean_jobs_at_launch'],(module,r['foreign_lean_jobs_at_launch'])
 objects[module.replace('/','.')]=r['object_sha256'];receipts[module]=r
 results[module]={k:r[k] for k in ['source_revision','source_sha256','object_sha256','features','command','exit_status','wall_seconds','peak_rss_kib','process_swaps','cgroup_swap_bytes','print_axioms_output']}
 results[module].update(attempt=attempt,receipt_sha256=sha(rp.read_bytes()))
reused=json.loads((tool/'s2-reused-table-objects.json').read_text())
for module,p in reused['entries'].items():
 rp=repo/p['receipt'];r=json.loads(rp.read_text())
 assert sha(rp.read_bytes())==p['receipt_sha256'] and r['exit_status']==0
 assert sha((area/'lean'/(module+'.lean')).read_bytes())==p['source_sha256']==r['source_sha256']
 assert r['object_sha256']==p['object_sha256'];objects[module]=p['object_sha256']
 assert 'sorryAx' not in r['print_axioms_output']
for module,r in receipts.items():
 for d in r['direct_imports']:
  if d['module'] in objects:assert d['sha256']==objects[d['module']],(module,d)
# Digest32-style re-pin inventory for both changed owners, including all emitted
# nested bodies/loops (old reference and new fast path/fallbacks).
names=re.findall(r'(?m)^def\s+([A-Za-z_][A-Za-z_0-9.]*)',(tool/'s2-groups-generated/Funs.lean').read_text());declarations=[]
for name in ['grouped_inactive_pair','s2_grouped_inactive_pair']:
 a,b,data=item(cur,name)
 starts=('new.'+name,'old.'+name)
 declarations.append(dict(classification='new-source-bound',cone='S2-inactive-group-pairing',rust_owner='weights::'+name,kind='fun_decls',source_path=path,current_start_byte=a,current_end_byte_exclusive=b,current_file_sha256=sha(cur),source_text_sha256=sha(data),historical_llbc_source_file=path,historical_span={'beg':{'line':cur[:a].count(b'\n')+1,'col':0},'end':{'line':cur[:b].count(b'\n')+1,'col':1}},extracted_lean_declarations=['AspisR1S2Groups.'+n for n in names if n.startswith(starts)],statement_diff='',notes='Exact helper source with extraction namespace/public visibility only; unchanged computational arithmetic/decoder parameterized without laws. Fixed classification tables and first-appearance order checked from actual source.'))
(ev/'S2-CANDIDATE3-DECLARATION-REPIN.json').write_text(json.dumps(dict(schema_reference='design/J1-DIGEST32-EXTRACTED-DECLARATION-REPIN-20261016.json',candidate=candidate,parent=parent,counts={'new-source-bound':2},declarations=declarations),indent=2)+'\n')
report=dict(candidate=candidate,parent=parent,frozen_production_revision=frozen,status='SOURCE_KERNEL_EQUIVALENCE_AND_UNCHANGED_CONTEXT_SUBSTITUTION_CHECKED',successes=results,reused_tables=reused,contexts=contexts,production_source_changed=False,measured_stage1_saving_cu=0,measured_settlement_saving_cu=[40517,40520],runtime_evidence='../cu-savings-20261019/FINAL-REPORT.md',assumptions=['Existing Rust/Charon/Aeneas translation and coherent primitive/runtime semantics; sufficient stack/resources.','Identical shared computational arithmetic/decoder/formatting operations, with no equivalence, success, canonicality or algebraic laws assumed.','Inherited core.fmt.Formatter is Type-valued, not a soundness proposition.','Production features pool-adapter,private-leaf-salts; r0-op-count disabled.'],audit=dict(command=[sys.executable,*sys.argv],source_revision=git('rev-parse','HEAD').decode().strip(),features=[],exit_status=0,wall_seconds=time.monotonic()-started,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss//1024,process_swaps=resource.getrusage(resource.RUSAGE_SELF).ru_nswap,print_axioms='N/A: source/receipt audit; full Lean outputs in successes.'))
(ev/'S2-CANDIDATE3-FINAL.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(dict(status=report['status'],lean_targets=len(results),reused_tables=len(reused['entries']),changed_owners=2,new_equivalence_axioms=0)))
