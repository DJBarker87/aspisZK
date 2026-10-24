#!/usr/bin/env python3
"""Audit only owned outputs/inputs; never invoke Lean or reopen donors."""
import ast,collections,hashlib,json,resource,subprocess,sys,time
from pathlib import Path
T=Path(__file__).resolve().parent;R=T.parents[1];E=R/'evidence/port28rootexport-20261024'
def pin(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return dict(path=str(p),sha256=h.hexdigest(),bytes=p.stat().st_size)
def write(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def main():
 start=time.monotonic();runpath=E/'Port28ROOTEXPORT_lean2.receipt.json';run=json.loads(runpath.read_text())
 pre=json.loads((E/'Port28ROOTEXPORT_correction-preflight.json').read_text());data=Path(pre['retained'])
 assert run['exit_status'] is not None and run['lean_invocations_charged']==1
 assert pin(T/'Port28ROOTEXPORT_Raw.lean')==run['tool']
 assert pin(Path(pre['full_manifest']['path']))==pre['full_manifest']
 full=json.loads(Path(pre['full_manifest']['path']).read_text())
 for x in full['object_parts']:
  p=Path(x['retained_path']);assert p.is_file() and not p.is_symlink() and p.stat().st_nlink==1
  q=pin(p);assert q['sha256']==x['sha256'] and q['bytes']==x['bytes']
 for x in full['inputs']:assert pin(Path(x['path']))==x
 for field in ['stdout','stderr_time']:
  q=pin(Path(run[field+'_path']));assert q['sha256']==run[field]['sha256'] and q['bytes']==run[field]['bytes']
 time_text=Path(run['stderr_time_path']).read_text()
 run['maximum_resident_set_size_bytes']=int(next(l.split()[0] for l in time_text.splitlines() if 'maximum resident set size' in l))
 run['swaps']=int(next(l.split()[0] for l in time_text.splitlines() if l.strip().endswith(' swaps')))
 write(runpath,run)
 (E/'Port28ROOTEXPORT_lean2.time.log').write_text(time_text)
 stdout=Path(run['stdout_path']);headers={};edges={};groups={};transports={};safety={};core=collections.defaultdict(set);rounds=[];unresolved=None;summary=None;errors=[];counts=collections.Counter()
 for line in stdout.open():
  tag,sep,raw=line.rstrip('\n').partition(' ')
  if tag not in ['HEADER','EDGE','GROUP','TRANSPORT','SAFETY','CORE_LEAF','ROUND','UNRESOLVED','SUMMARY']:
   if 'error:' in line or 'failed' in line:errors.append(line.rstrip())
   continue
  x=json.loads(raw);counts[tag]+=1
  arity={'HEADER':3,'EDGE':4,'GROUP':5,'TRANSPORT':4,'SAFETY':5,'CORE_LEAF':2,'ROUND':3,'SUMMARY':5}.get(tag)
  if arity is not None:
   fields=[]
   for _ in range(arity-1):
    assert isinstance(x,list) and len(x)==2,(tag,x)
    fields.append(x[0]);x=x[1]
   x=fields+[x]
  if tag=='HEADER':headers[(x[0],x[1])]=x[2]
  elif tag=='EDGE':edges[(x[0],x[1],x[2])]=x[3]
  elif tag=='GROUP':groups[(x[0],x[1],x[2])]=x
  elif tag=='TRANSPORT':transports[(x[0],x[1])]=x
  elif tag=='SAFETY':safety[(x[0],x[1],x[2])]=x[3:]
  elif tag=='CORE_LEAF':core[x[0]].add(x[1])
  elif tag=='ROUND':rounds.append(x)
  elif tag=='UNRESOLVED':unresolved=x
  elif tag=='SUMMARY':summary=x
 plan=json.loads((E/'Port28ROOTEXPORT_seed-plan.json').read_text());seednames={x['name'] for x in plan['seeds']}
 selected={n for o,m,n in edges};required=set(seednames)
 for ds in edges.values():required.update(ds)
 missing=sorted(seednames-selected);calculated=sorted(required-selected-set(core))
 unsafe=[dict(origin=o,module=m,name=n,isUnsafe=v[0],isPartial=v[1]) for (o,m,n),v in safety.items() if any(v)]
 origins=collections.defaultdict(list)
 transport_pins=[]
 for (o,m),x in transports.items():
  p=Path(x[2]);assert p.is_relative_to(data/'transports') and not p.is_symlink()
  transport_pins.append(dict(origin=o,module=m,**pin(p),names=x[3]))
  for n in x[3]:origins[n].append(dict(origin=o,module=m,path=str(p)))
 duplicates={n:xs for n,xs in origins.items() if len(xs)>1}
 transport_hashes={x['path']:x['sha256'] for x in transport_pins}
 duplicate_transport_byte_status={n:('IDENTICAL full raw transport bytes' if len({transport_hashes[x['path']] for x in xs})==1 else 'DIFFERENT containing transport bytes; per-declaration equality UNRESOLVED') for n,xs in duplicates.items()}
 if run['exit_status']==0:
  assert summary is not None and unresolved is not None
  assert calculated==sorted(unresolved)
  assert selected=={n for x in transports.values() for n in x[3]}
  assert len(selected)==summary[2] and len(core)==summary[3] and len(unresolved)==summary[4]
 seed_edges=collections.defaultdict(set)
 for (o,m,n),ds in edges.items():seed_edges[n].update(ds)
 reachable=set();pending=list(seednames)
 while pending:
  n=pending.pop()
  if n in reachable:continue
  reachable.add(n);pending.extend(seed_edges[n]-reachable)
 flagged={x['name'] for x in unsafe}
 seed_audit=dict(seed_count=len(seednames),reachable_names=len(reachable),reachable_flagged_raw_auxiliaries=sorted(reachable&flagged),flagged_source_seeds=sorted(seednames&flagged),unresolved_reachable_names=sorted(reachable&set(unresolved or [])),note='Names/edges only. No safe logical reconstruction or project-axiom rejection. Main core .olean constNames scanned; pinned .server/.private not inventoried. Unresolved does not mean proved absent or noncore.')
 write(E/'Port28ROOTEXPORT_logical-seed-audit.json',seed_audit)
 all_transports=[pin(p) for p in sorted((data/'transports').rglob('*.olean'))] if (data/'transports').exists() else []
 detail=dict(schema='Port28ROOTEXPORT-correction-output-audit-v1',headers=[dict(origin=o,module=m,imports=ds) for (o,m),ds in headers.items()],
  edges=[dict(origin=o,module=m,name=n,dependencies=ds) for (o,m,n),ds in edges.items()],groups=list(groups.values()),
  final_round_transports=transport_pins,all_round_transports=all_transports,core_leaves={n:sorted(ps) for n,ps in core.items()},
  duplicate_name_origins=duplicates,duplicate_containing_transport_bytes=duplicate_transport_byte_status,strict_duplicate_declaration_equality='UNRESOLVED: full declarations retained, not compared by this exporter or Python; no first-wins accepted',
  safety_flags=unsafe,missing_seeds=missing,unresolved_emitted=unresolved,unresolved_recomputed=calculated,rounds=rounds,summary=summary,
  original_object_inputs=full['object_parts'],source_manifest=pin(E/'Port28ROOTEXPORT_sources.json'),seed_manifest=pin(E/'Port28ROOTEXPORT_seed-plan.json'),
  reused_input_manifest=pre['full_manifest'],active_tool=run['tool'],historical_tool=pre['historical_failed_source'],runtime=run['runtime'],run_receipt=pin(runpath),stdout=pin(stdout),prior_final_data_manifest=json.loads((E/'Port28ROOTEXPORT_data-summary.json').read_text())['full_data_manifest'])
 detailpath=data/'correction-output-audit.json';write(detailpath,detail)
 audit=dict(status='Diagnostic exit0; output consistency audit PASS; closure INCOMPLETE' if run['exit_status']==0 else 'Diagnostic FAILED; available outputs audited without retry',
  exit_status=run['exit_status'],stop_reason=run.get('stopped'),errors=errors,run_receipt='Port28ROOTEXPORT_lean2.receipt.json',output_audit_manifest=pin(detailpath),stdout=pin(stdout),
  event_counts=dict(counts),rounds=rounds,summary=summary,final_transport_files=len(transports),all_round_transport_files=len(all_transports),all_round_transport_bytes=sum(x['bytes'] for x in all_transports),partial_unindexed_transports=(summary is None and bool(all_transports)),
  selected_unique_names=len(selected),selected_origin_declarations=len(edges),missing_seed_names=missing,
  unresolved_count=None if unresolved is None else len(unresolved),unresolved_names=unresolved,unresolved_meaning='323 names not resolved by this exporter; core .server/.private pinned but not inventoried; not all proved missing or noncore.',logical_seed_audit=pin(E/'Port28ROOTEXPORT_logical-seed-audit.json'),
  standard_core_leaf_names=len(core),duplicate_name_groups=len(duplicates),duplicate_byte_identical_transport_groups=sum(v.startswith('IDENTICAL') for v in duplicate_transport_byte_status.values()),duplicate_unresolved_transport_groups=sum(v.startswith('DIFFERENT') for v in duplicate_transport_byte_status.values()),strict_duplicate_equality='UNRESOLVED; all variants retained for separately authorized full-declaration consumer',
  raw_unsafe_partial=unsafe,safe_logical_seed_status='Seeds available only if missing_seed_names empty; unsafe/partial compiler auxiliaries are raw data, never approved logical seeds. Consumer must select/reconstruct safe logical closure and retain rejection policy.',
  input_objects=len(full['object_parts']),input_modules=len({x['module'] for x in full['object_parts']}),input_bytes=sum(x['bytes'] for x in full['object_parts']),
  charged_this_correction=1,total_job_lean_invocations=2,global_known_actual_after=349,global_limit=368,
  remaining=dict(unassigned=7,reserved_actual_consumer=5,former_Port24_carry=7,pending_here=0),other_new_compiler_host_build_scope_invocations=0,
  print_axioms='N/A: untrusted raw data diagnostic and noncompiler audit, no theorem',
  old_source_preflight='REUSED PASS, not rerun; original failed source/logs/receipts unchanged',
  sourcecuts_status='No new immutable owner proof result reviewed here; no current witness mismatch asserted. Whole join remains open.',
  claims='No kernel/source/native/current-SDK/whole-cone/release/security claim. Both targets not yet established.',
  next_prerequisite='Locate unresolved names in complete pinned part inventories, including core .server/.private; obtain missing original parts only if actually absent, strict duplicate full-ConstantInfo comparison with explicit variant selection, then separately authorized original/CURRENT declaration and actual caller/event/mark join including reviewed proof refresh; reconstruct safe logical closure.',
  audit_exit_status=0,audit_script=pin(Path(__file__).resolve()),audit_command=['python3','-B',str(T/'Port28ROOTEXPORT_audit-correction.py')],audit_wall_seconds=time.monotonic()-start,audit_peak_rss_bytes=resource.getrusage(0).ru_maxrss,audit_swaps=resource.getrusage(0).ru_nswap,
  audit_python_runtime=dict(version=sys.version,executable=pin(Path(sys.executable).resolve())),audit_source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
 write(E/'Port28ROOTEXPORT_correction-audit.json',audit)
 m=json.loads((E/'Port28ROOTEXPORT_manifest.json').read_text());m.update(status=audit['status'],correction_report='Port28ROOTEXPORT_CORRECTION-REPORT.md',correction_audit='Port28ROOTEXPORT_correction-audit.json',new_lean_invocations=2,unused_allocated_lean_slots=0,raw_data_output_manifest=audit['output_audit_manifest'],strict_duplicate_equality=audit['strict_duplicate_equality'],new_print_axioms=audit['print_axioms'],transports=dict(final_files=len(transports),retained_manifest=audit['output_audit_manifest']),emitted_declarations=dict(unique_names=len(selected),origin_entries=len(edges),missing_seed_names=missing),historical_first_attempt_summary='Port28ROOTEXPORT_data-summary.json; unchanged historical failed-attempt state')
 write(E/'Port28ROOTEXPORT_manifest.json',m)
 for p in T.glob('*.py'):ast.parse(p.read_text())
 paths=subprocess.check_output(['git','diff','--name-only','438e20f4e4f8596b2d812f6f98a7f5b285827dc0'],text=True).splitlines()
 assert all(p.startswith(('tools/port28rootexport-20261024/','evidence/port28rootexport-20261024/')) for p in paths)
 assert all(p.stat().st_size<=5_000_000 for d in [T,E] for p in d.iterdir() if p.is_file())
 print(json.dumps({k:audit[k] for k in ['status','errors','summary','final_transport_files','selected_unique_names','missing_seed_names','unresolved_count','duplicate_name_groups','raw_unsafe_partial','audit_wall_seconds','audit_peak_rss_bytes']}))
if __name__=='__main__':main()
