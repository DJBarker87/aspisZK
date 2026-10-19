from pathlib import Path
import datetime, gzip, hashlib, io, json, re, tarfile
root=Path.cwd()
p=root/'docs/research/100bit-spend-path-20261013/evidence/lean-semantic-prefix-agreement-20261015'
sha=lambda f:hashlib.sha256(Path(f).read_bytes()).hexdigest()
# Preserve the superseded summary; original run receipts are never edited.
old=p/'manifest-local-failures.json'
if not old.exists(): old.write_bytes((p/'manifest.json').read_bytes())
object_bytes={f.name:f.read_bytes() for f in sorted((p/'host-objects').glob('*.olean'))}
assert len(object_bytes)==3
buf=io.BytesIO()
with tarfile.open(fileobj=buf, mode='w') as out:
 for name,data in object_bytes.items():
  info=tarfile.TarInfo(name); info.size=len(data); info.mtime=0; info.mode=0o644
  out.addfile(info,io.BytesIO(data))
with (p/'new-objects.tar.gz').open('wb') as f:
 with gzip.GzipFile(filename='',mode='wb',fileobj=f,mtime=0) as g:g.write(buf.getvalue())
archive_shas={k:hashlib.sha256(v).hexdigest() for k,v in object_bytes.items()}
input_by_sha={sha(f):str(f.relative_to(p)) for f in (p/'host-inputs').glob('*.json')}
runner_by_sha={sha(f):str(f.relative_to(p)) for f in (p/'host-runner-history').glob('*.py')}
final_names=['primitive-linux-d','completed-linux-a','cut-linux-a']
final=[]; history=[]
for folder in sorted((p/'host-runs').iterdir()):
 r=json.loads((folder/'receipt.json').read_text())
 assert sha(folder/'source.lean')==r['source_sha256']
 assert r['runner_sha256'] in runner_by_sha
 assert r['input_manifest_sha256'] in input_by_sha
 h={'attempt':folder.name,'receipt':str((folder/'receipt.json').relative_to(p)),
    'runner':runner_by_sha[r['runner_sha256']], 'input_manifest':input_by_sha[r['input_manifest_sha256']],
    'exit_status':r['exit_status'],'source_sha256':r['source_sha256']}
 history.append(h)
 if folder.name not in final_names:continue
 canonical=root/'docs/research/100bit-spend-path-20261013/lean'/f"{r['target'][2:]}.lean"
 assert sha(canonical)==r['source_sha256']
 assert archive_shas[r['target']+'.olean']==r['olean_sha256']
 assert r['exit_status']==0 and r['process_swaps']==0 and r['cgroup_swap_current']=='0'
 assert r['memory_events_before']==r['memory_events_after']
 assert r['limits']=={'memory.max':'8589934592','memory.high':'6442450944','memory.swap.max':'0'}
 log=(folder/'lean.log').read_text()
 reports=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",log,re.S)
 expected_count={'primitive-linux-d':3,'completed-linux-a':4,'cut-linux-a':2}[folder.name]
 assert len(reports)==expected_count and 'sorryAx' not in log
 axioms={name:[x.strip() for x in values.split(',')] for name,values in reports}
 assert all(set(xs)<= {'propext','Classical.choice','Quot.sound'} for xs in axioms.values())
 final.append({**h,'target':r['target'],'source':str(canonical.relative_to(root)),
  'wall_seconds':r['wall_seconds'],'peak_process_rss_kib':r['peak_process_rss_kib'],
  'cgroup_memory_peak_bytes':int(r['cgroup_memory_peak']),'process_swaps':0,'cgroup_swap_current_bytes':0,
  'object_sha256':r['olean_sha256'],'axioms':axioms})
# Keep loose copies only in the private working area; the commit contains a small archive.
saved=root/'.semantic-prefix-check/final-host-objects';saved.mkdir(exist_ok=True)
for f in (p/'host-objects').glob('*.olean'):
 (saved/f.name).write_bytes(f.read_bytes());f.unlink()
(p/'host-objects').rmdir()
m={
 'packaged_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'source_revision':'b40d1cfffadbdf967f84cca23ea4e7f1553d564f',
 'requested_ancestor':'b8760b76ac8de6c5c903eb98ff3a85f6f9f532e8',
 'status':'Three new modules checked successfully on Lean4.32; all nine theorem axioms audits standard-only. Conditional representation agreement only.',
 'accepted_attempts':final,'host_attempt_history':history,
 'preserved_local_failures':['completed-a.json','agreement-a.json','agreement-core-a.json'],
 'preflight_manifests':'Immutable historical input snapshots can say unverified; accepted_attempts and their final receipts supersede that preflight status only.',
 'failed_axioms':'primitive-linux-c exited1 and reports sorryAx for decoded_length; it is not accepted. Final corrected primitive-linux-d is clean.',
 'configuration_changes':[
  'First local predecessor attempt omitted explicit -j1; subsequent local attempts used -j1 and the same -M3500/4GiB sampled cap.',
  'Two missing unchanged predecessor objects recovered from exact-source historical artifacts; no dependency rebuilt.',
  'Combined target split into core+cut, then primitive+completed+cut; all failed receipts and source snapshots preserved.',
  'Host import-only baseline failed before bridge proofs at -M3500/hard4GiB; changed primitive partition failed at -M6000/hard8GiB.',
  'Pinned runtime process-RSS accounting and observed RSS/cgroup discrepancy motivated a new primitive import diagnostic with -M0 at unchanged hard8GiB cgroup cap.',
  'Diagnostic passed. Primitive theorem then exposed a dependent inference error; explicit typed decode input fixed it before final successful checks.'
 ],
 'resource_accounting':{
  'final_hard_limits':{'MemoryHigh':6442450944,'MemoryMax':8589934592,'MemorySwapMax':0},
  'final_lean_options':['-j1','-M0'],
  'interpretation':'Shared imported-page charging is consistent with the observed RSS/cgroup discrepancy; precise attribution is an inference. The hard cgroup cap remained active when the redundant internal RSS limit was disabled.',
  'runtime_source':'https://raw.githubusercontent.com/leanprover/lean4/8c9756b28d64dab099da31a4c09229a9e6a2ef35/src/runtime/memory.cpp',
  'cgroup_source':'https://docs.kernel.org/admin-guide/cgroup-v2.html#memory-ownership',
 },
 'dependency_rebuild':False,'full_manifest_replay':False,
 'import_partition':json.loads((p/'host-inputs/input-manifest.json').read_text())['import_footprint'],
 'dependency_provenance':'374 existing macOS project objects reused with exact source/object pins in host-inputs. None are included in new-objects.tar.gz.',
 'runtime_provenance':'runtime.json preserves local version/dylib hashes; every host receipt records Linux --version and libleanshared*.so hashes.',
 'object_archive':{'path':'new-objects.tar.gz','sha256':sha(p/'new-objects.tar.gz'),'members':archive_shas},
 'remaining_boundaries':['Typed-byte decoding success remains a premise of success corollaries.','Typed-cut success and already-read address membership remain premises of cut corollaries.','C2 recovery and exact table/fallback challenge provenance are supplied, not established.','No actual Rust refinement, live caller reachability, acceptance, extraction, D3 or soundness closure claim.'],
 'files':{str(f.relative_to(p)):sha(f) for f in sorted(p.rglob('*')) if f.is_file() and f.name!='manifest.json'}
}
(p/'manifest.json').write_text(json.dumps(m,indent=2)+'\n')
print('Verified final modules:',len(final),'axioms:',sum(len(x['axioms']) for x in final))
print('Archive bytes:',(p/'new-objects.tar.gz').stat().st_size,'evidence files:',len(m['files'])+1)
print('All historical host source, runner and input manifest hashes match.')
