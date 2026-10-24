#!/usr/bin/env python3
"""Final new-data audit. Own captures only; no SSH/Lean/old source preflight."""
import ast,collections,hashlib,json,resource,subprocess,sys,time
from pathlib import Path
T=Path(__file__).resolve().parent;R=T.parents[1];E=R/'evidence/port28rootexport-20261024'
def pin(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
    return dict(path=str(p),sha256=h.hexdigest(),bytes=p.stat().st_size)
def write(p,x):
    raw=(json.dumps(x,indent=2)+'\n').encode();assert len(raw)<=5_000_000;p.write_bytes(raw)
def main():
    start=time.monotonic()
    for p in T.glob('*.py'):ast.parse(p.read_text())
    old=json.loads((E/'Port28ROOTEXPORT_copy-failed-v1.json').read_text())
    new=json.loads((E/'Port28ROOTEXPORT_copy.json').read_text())
    run=json.loads((E/'Port28ROOTEXPORT_lean.receipt.json').read_text())
    retained=Path(new['retained']);objects=old['objects']+new['objects']
    assert old['exit_status']==1 and new['exit_status']==0
    for x in objects:
        p=Path(x['retained_path']);assert p.is_file() and not p.is_symlink() and p.stat().st_nlink==1
        assert pin(p)['sha256']==x['sha256']==x['copy_sha256']==x['post_sha256']
    for field in ['stdout','stderr_time']:
        p=Path(run[field+'_path']);observed=pin(p)
        assert observed['sha256']==run[field]['sha256'] and observed['bytes']==run[field]['bytes']
    assert run['lean_invocations_charged']==1 and run['exit_status']==1
    stdout=Path(run['stdout_path']).read_text()
    assert ':57:74: error:' in stdout and ':77:2: error:' in stdout
    assert not any(line.startswith(('HEADER ','EDGE ','TRANSPORT ')) for line in stdout.splitlines())
    assert not (retained/'transports').exists()
    (E/'Port28ROOTEXPORT_lean.stdout.log').write_text(stdout)
    time_text=Path(run['stderr_time_path']).read_text();(E/'Port28ROOTEXPORT_lean.time.log').write_text(time_text)
    run['maximum_resident_set_size_bytes']=int(next(l.split()[0] for l in time_text.splitlines() if 'maximum resident set size' in l))
    run['swaps']=int(next(l.split()[0] for l in time_text.splitlines() if l.strip().endswith(' swaps')))
    write(E/'Port28ROOTEXPORT_lean.receipt.json',run)
    assert pin(T/'Port28ROOTEXPORT_Raw.lean')['sha256']==run['tool']['sha256']
    bymodule=collections.defaultdict(list)
    for x in objects:bymodule[x['module']].append(x)
    duplicates={m:dict(status='IDENTICAL raw object bytes' if len({x['sha256'] for x in xs})==1 else 'DIFFERENT raw object bytes; no ConstantInfo comparison available',origins=[dict(path=x['path'],sha256=x['sha256'],retained_path=x['retained_path']) for x in xs]) for m,xs in bymodule.items() if len(xs)>1}
    streams=[];exclusions=[];missing_roots=[];remote_metrics=[];absent_parts=[]
    for capture in [old,new]:
        p=Path(capture['retained'])/'stream.jsonl';assert pin(p)['sha256']==capture['stream_sha256']
        streams.append(pin(p))
        for line in p.open():
            x=json.loads(line)
            if x['kind']=='excluded-symlink':exclusions.append(x)
            if x['kind']=='missing-root':missing_roots.append(x)
            if x['kind']=='absent-part':absent_parts.append(x)
            if x['kind']=='remote-receipt':remote_metrics.append(x)
            if x['kind']=='during-observation':assert x['observation']['allowed_to_enter']
    graph=json.loads((E/'Port28ROOTEXPORT_source-import-plan.json').read_text())
    plan=json.loads((E/'Port28ROOTEXPORT_seed-plan.json').read_text())
    gaps=sorted(set(graph['modules'])-set(bymodule))
    seed_modules={s['module'] for s in plan['seeds']};assert seed_modules<=set(bymodule)
    input_manifest=pin(retained/'diagnostic-inputs.json');assert input_manifest==json.loads((E/'Port28ROOTEXPORT_diagnostic-preflight.json').read_text())['full_manifest']
    data=dict(schema='Port28ROOTEXPORT-copied-original-data-v1',objects=objects,streams=streams,raw_object_duplicate_origins=duplicates,
        excluded_symlink_origins=exclusions,missing_roots=missing_roots,absent_optional_parts=absent_parts,
        source_import_modules_without_regular_copies=gaps,external_source_import_frontier=graph['external_or_missing_source_modules'],
        seed_source_declarations=plan['seeds'],remote_success_metrics=remote_metrics,
        constantinfo_names_edges_groups_unresolved='NOT COMPUTED: sole diagnostic failed before IO',
        constantinfo_duplicate_conflicts='NOT COMPUTED; raw object variants retained, no first-wins acceptance',
        transports=[],historical_main_pins=plan['historical_direct_object_pins'],diagnostic_inputs=input_manifest)
    raw=json.dumps(data,indent=2).encode();(retained/'final-data-manifest.json').write_bytes(raw)
    summary=dict(schema='Port28ROOTEXPORT-resumed-data-summary-v1',status='ROOT donor files copied/pinned; raw ConstantInfo export FAILED before IO; slot exhausted',
        new_private_object_files=len(objects),unique_modules=len(bymodule),object_bytes=sum(x['bytes'] for x in objects),
        main_parts=len(objects),server_private_parts_copied=0,required_seed_modules_present=sorted(seed_modules),
        source_import_modules_without_regular_copies=gaps,excluded_symlink_origins=len(exclusions),missing_roots=missing_roots,
        duplicate_module_groups=len(duplicates),raw_byte_variant_groups=sum(d['status'].startswith('DIFFERENT') for d in duplicates.values()),
        full_data_manifest=pin(retained/'final-data-manifest.json'),streams=streams,diagnostic_inputs=input_manifest,
        new_lean_invocations=1,allocated_lean_slots=1,unused_allocated_lean_slots=0,five_consumer_slots='held; untouched',
        other_compiler_build_kani_extraction_backend_elf_scope_invocations=0,
        declaration_inventory_edges_groups_closure='NOT COMPUTED; no diagnostic IO occurred',
        transports=[],constantinfo_duplicate_conflicts='NOT COMPUTED; all acquired raw variants retained',
        historical_source_assessment='Immutable original sources and lean109/110 receipts REUSED; three current main objects match direct historical pins. Other current donor observations and optional-part absence are not historical output/source materialization pins.',
        unresolved_data='Full emitted/private/generated group and type/value closure still require a corrected separately allocated core diagnostic. Unknown linked origins remain excluded. Current A was not accessed and did not block this ROOT-side run.',
        runtime_gaps='Host Python interpreter version/metrics observed; binary and full loaded-runtime mapping not sealed. Local Lean executable/dylibs and core parts pinned in diagnostic-inputs.json; these are current observations.',
        semantic_split_gap='Remains the next concrete same-tuple/lower-constructor proof obligation, not the reason data export failed.',
        assumptions='unchanged; none discharged/added',print_axioms='N/A: raw-data copy and failed diagnostic; no theorem',
        claims='No kernel/current-SDK/source-native/whole-cone/release/security conclusion. Both security targets and whole experiment not established.')
    write(E/'Port28ROOTEXPORT_data-summary.json',summary)
    m=json.loads((E/'Port28ROOTEXPORT_manifest.json').read_text())
    m.update(status=summary['status'],new_object_observations=dict(count=len(objects),manifest=summary['full_data_manifest']),
        new_lean_invocations=1,unused_allocated_lean_slots=0,host_accesses='Read-only metadata and regular-object copies; exact commands in operation receipts',
        current_data_summary='Port28ROOTEXPORT_data-summary.json',transports=[],emitted_declarations=[],new_print_axioms=summary['print_axioms'])
    write(E/'Port28ROOTEXPORT_manifest.json',m)
    paths=subprocess.check_output(['git','diff','--name-only','5de60d6c748ffce8d2c40984f7baeb7af86feb16'],text=True).splitlines()
    assert all(p.startswith(('tools/port28rootexport-20261024/','evidence/port28rootexport-20261024/')) for p in paths)
    u=resource.getrusage(0)
    receipt=dict(command=['python3','-B',str(T/'Port28ROOTEXPORT_finalize.py')],exit_status=0,wall_seconds=time.monotonic()-start,peak_rss_bytes=u.ru_maxrss,swaps=u.ru_nswap,
        source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,python_runtime=dict(version=sys.version,executable=pin(Path(sys.executable).resolve())),
        status='PASS new own-capture/manifest/source audit; old source-only preflight reused, not rerun',
        files=[pin(p) for d in [T,E] for p in sorted(d.iterdir()) if p.is_file() and p.name!='Port28ROOTEXPORT_final-audit.json'],
        no_remote_reread=True,no_lean_rerun=True,print_axioms='N/A: no theorem')
    assert all(x['bytes']<=5_000_000 for x in receipt['files'])
    write(E/'Port28ROOTEXPORT_final-audit.json',receipt)
    print(json.dumps(dict(status=receipt['status'],objects=len(objects),unique_modules=len(bymodule),object_bytes=summary['object_bytes'],raw_transports=0,lean_used=1,source_gaps=gaps,byte_variant_module_groups=summary['raw_byte_variant_groups'],wall_seconds=receipt['wall_seconds'],peak_rss_bytes=u.ru_maxrss,swaps=u.ru_nswap)))
if __name__=='__main__':main()
