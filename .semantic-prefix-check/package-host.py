import datetime, hashlib, json, shutil, tarfile
from pathlib import Path

here = Path(__file__).resolve().parent
work = here.parent
evidence = work/'docs/research/100bit-spend-path-20261013/evidence/lean-semantic-prefix-agreement-20261015'
original = json.loads((evidence/'import-source-pins.json').read_text())
reused = {x['module']: x for x in json.loads((here/'reused-predecessors.json').read_text())}
bundle = here/'host-bridge'
sources, objects = bundle/'sources', bundle/'objects'
sources.mkdir(parents=True, exist_ok=True)
objects.mkdir(parents=True, exist_ok=True)
pins = {}
for module, entry in original['modules'].items():
    if module == 'R1SemanticPrefixAgreement':
        continue
    source = work/entry['source']
    source_hash = hashlib.sha256(source.read_bytes()).hexdigest()
    assert source_hash == entry['source_sha256'], module
    obj = Path(entry['object']) if 'object' in entry else here/'objects'/(module+'.olean')
    object_hash = hashlib.sha256(obj.read_bytes()).hexdigest()
    assert object_hash == entry.get('object_sha256', reused.get(module, {}).get('object_sha256')), module
    relative = Path(*module.split('.'))
    target_source = sources/relative.with_suffix('.lean')
    target_object = objects/relative.with_suffix('.olean')
    target_source.parent.mkdir(parents=True, exist_ok=True)
    target_object.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(source, target_source)
    shutil.copyfile(obj, target_object)
    pins[module] = dict(entry, source_snapshot=str(target_source.relative_to(bundle)), object_snapshot=str(target_object.relative_to(bundle)), object_original_path=str(obj), object_sha256=object_hash, reused_predecessor_provenance=reused.get(module))
targets = {}
for module in ['R1SemanticPrefixAgreement', 'R1SemanticPrefixCutAgreement']:
    source = work/'docs/research/100bit-spend-path-20261013/lean'/(module.removeprefix('R1')+'.lean')
    target = sources/(module+'.lean')
    shutil.copyfile(source, target)
    targets[module] = {'source': str(source.relative_to(work)), 'source_snapshot': str(target.relative_to(bundle)), 'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(), 'status': 'unverified; no successful object exists'}
artifacts = bundle/'local-evidence'
artifacts.mkdir(exist_ok=True)
for name in ['runtime.json', 'reused-predecessors.json', 'completed-a.json', 'completed-a.log', 'completed-a.source.lean', 'agreement-a.json', 'agreement-a.log', 'agreement-a.source.lean', 'agreement-core-a.json', 'agreement-core-a.log', 'agreement-core-a.source.lean', 'run-focused.py', 'lean-with-cache.py']:
    shutil.copyfile(here/name, artifacts/name)
diagnostic = sources/'R1SemanticPrefixImportBaseline.lean'
diagnostic.write_text('import R1SemanticPrefixCodec\nimport R1SelectedCompletedSemantic\n\n#check AspisR1.SelectedSemanticPrefix.read\n')
manifest = {'created_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'source_revision': original['base'], 'existing_project_dependency_count': len(pins), 'new_targets': targets, 'dependency_pins': pins, 'scope': 'Existing objects are copied without rebuild; original locations, cache source comparisons and historical predecessor attestations are preserved. New core and typed-cut modules remain unverified after local resource-limited runs. Empty local logs do not distinguish import loading from first-proof elaboration. Root owns all host execution. The host must provide its existing exact Lean4.32/mathlib81a5d257 toolchain and package cache; this archive is the project-object overlay only.', 'local_runtime': 'local-evidence/runtime.json', 'host_order': ['R1SemanticPrefixAgreement', 'R1SemanticPrefixCutAgreement'], 'import_only_diagnostic': {'module': 'R1SemanticPrefixImportBaseline', 'source_snapshot': str(diagnostic.relative_to(bundle)), 'source_sha256': hashlib.sha256(diagnostic.read_bytes()).hexdigest()}, 'import_footprint': {'combined_existing_dependencies': 374, 'split_core_existing_dependencies': 339, 'typed_cut_existing_dependencies': 374, 'typed_cut_additional_new_dependency': 'R1SemanticPrefixAgreement'}}
(bundle/'manifest.json').write_text(json.dumps(manifest, indent=2)+'\n')
(bundle/'input-manifest.json').write_text(json.dumps(manifest, indent=2)+'\n')
archive = here/'semantic-prefix-host-overlay.tar.gz'
with tarfile.open(archive, 'w:gz', compresslevel=1) as out:
    out.add(bundle, arcname='bridge')
receipt = {'archive': str(archive), 'sha256': hashlib.sha256(archive.read_bytes()).hexdigest(), 'bytes': archive.stat().st_size, 'project_dependency_objects': len(pins), 'new_source_targets': targets}
(here/'host-overlay-receipt.json').write_text(json.dumps(receipt, indent=2)+'\n')
print(json.dumps(receipt, indent=2))
