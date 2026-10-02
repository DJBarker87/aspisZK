#!/usr/bin/env python3
"""Read-only postbuild provenance and cache audit for the approved R363 clone."""
from datetime import datetime, timezone
from pathlib import Path
import hashlib, json, os, stat, time

ROOT = Path('/home/dombarker/project-offloads/aspis-r363-instantiated-pattern-candidate-20261002-a')
SRC = ROOT / 'src'
AUDIT = ROOT / 'candidate-audit'
BUILD_AUDIT = AUDIT / 'r363-build'
PARENT = Path('/home/dombarker/project-offloads/aspis-r360-comment-context-candidate-20261002-a')
PARENT_SRC = PARENT / 'src'
PREBUILD = AUDIT / 'R363-source-tree-manifest.json'
PARENT_BASELINE = PARENT / 'candidate-audit/postbuild-source-audit/candidate-current-manifest.json'
CLONE_AUDIT = AUDIT / 'clone-audit.json'
BUILD_RESULT = BUILD_AUDIT / 'build-result.json'
DOCKER_INSPECT = BUILD_AUDIT / 'docker-inspect.json'
CGROUP_SAMPLES = BUILD_AUDIT / 'cgroup-samples.json'
CANDIDATE_BINARY = ROOT / 'aeneas-r363-instantiated-pattern-candidate'
EXPECTED = {
    'prebuild_manifest': 'e43845424aeb6964281bd0d5e9d7ba4beb3d0a0aefe10b8acdab382127503e89',
    'parent_postbuild_manifest': 'f4182ab1431b1832a24ecee727c974f931962285d0783d64ff03633781a1ee89',
    'clone_audit': '7b0482d1ea4b068ece18267002cdcd7dd24689f18b6909e2964cbe6bb5bba275',
    'binary': '3dc9ad6de1af901c8ead41940ba97097a0cf06f82d27dbc7d7c5eac03695e329',
    'NameMatcher.ml': 'bdafe5b3f4a688d0fa0b4df7f2e8a3d907f70be9fdaf64420ea600ceab597aa8',
    'llbc/LlbcAstUtils.ml': '17cb1b5cd3e0cf119f4c4eee776e0fc49e2a39c6ee7abbaa339f70d466484b97',
    'ExtractTypes.ml': '0f8ee29aa89c9456ea6c266ff8d767dcb8a83af5bbe8096d04e53582cb32c527',
    'TranslateCore.ml': '4f5db3cd77a10a3861539958d7b8566f09e6bcc3b72981fcc40388611d639cb9',
    'InterpExpansion.ml': 'da68f59bc0240bad9862f0733aecd7265c239dbe988669d5d8ddddafc5a79b19',
    'PrePasses.ml': '09014aa93bffd2cafeebaf23d27a301d66986d9349f4cc9dca6e8d1dfe0ba7dd',
    'R360_NameMatcher.ml': '32c60e5ad98d4953790d2a4be557229be66951738ef8c4f8b25a170db21c4cef',
    'R360_LlbcAstUtils.ml': '5ac2c679b28df91d76b19a65d242b92916bfb3c2838b4f908a94d8bf244a8f84',
}

def sha_bytes(data): return hashlib.sha256(data).hexdigest()
def sha_file(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b''): h.update(chunk)
    return h.hexdigest()
def inventory(root):
    rows=[]
    for p in sorted(root.rglob('*')):
        rel=p.relative_to(root).as_posix(); st=p.lstat()
        if stat.S_ISLNK(st.st_mode): rows.append({'path':rel,'kind':'symlink','target':os.readlink(p),'mode':stat.S_IMODE(st.st_mode),'mtime_ns':st.st_mtime_ns})
        elif stat.S_ISDIR(st.st_mode): rows.append({'path':rel,'kind':'directory','mode':stat.S_IMODE(st.st_mode),'mtime_ns':st.st_mtime_ns})
        elif stat.S_ISREG(st.st_mode): rows.append({'path':rel,'kind':'file','size':st.st_size,'sha256':sha_file(p),'mode':stat.S_IMODE(st.st_mode),'mtime_ns':st.st_mtime_ns})
        else: raise RuntimeError(f'unsupported filesystem entry: {p}')
    return rows
def comparable(row): return {k:v for k,v in row.items() if k!='mtime_ns'}
def by_path(rows):
    out={r['path']:r for r in rows}
    if len(out)!=len(rows): raise RuntimeError('duplicate manifest path')
    return out
def differences(a,b):
    am,bm=by_path(a),by_path(b)
    return [p for p in sorted(am.keys()|bm.keys()) if p not in am or p not in bm or comparable(am[p])!=comparable(bm[p])]
def nonbuild(paths): return [p for p in paths if not (p=='_build' or p.startswith('_build/'))]
def regular_inodes(root):
    result=set()
    for p in root.rglob('*'):
        if p.is_symlink(): continue
        st=p.stat(follow_symlinks=False)
        if stat.S_ISREG(st.st_mode): result.add((st.st_dev,st.st_ino))
    return result

started=datetime.now(timezone.utc).isoformat(timespec='microseconds')
for p in (SRC,PARENT_SRC,PREBUILD,PARENT_BASELINE,CLONE_AUDIT,BUILD_RESULT,DOCKER_INSPECT,CGROUP_SAMPLES,CANDIDATE_BINARY):
    assert p.exists(), f'missing required saved input: {p}'
pre_bytes=PREBUILD.read_bytes(); parent_bytes=PARENT_BASELINE.read_bytes(); clone_bytes=CLONE_AUDIT.read_bytes()
assert sha_bytes(pre_bytes)==EXPECTED['prebuild_manifest']
assert sha_bytes(parent_bytes)==EXPECTED['parent_postbuild_manifest']
assert sha_bytes(clone_bytes)==EXPECTED['clone_audit']
pre=json.loads(pre_bytes); parent_saved=json.loads(parent_bytes); clone=json.loads(clone_bytes)
assert clone['changed_source_paths_vs_R360']==['src/NameMatcher.ml','src/llbc/LlbcAstUtils.ml']
assert clone['shared_regular_file_inodes']==0
cand=inventory(SRC); parent=inventory(PARENT_SRC)
postbuild_delta=differences(cand,pre)
assert not nonbuild(postbuild_delta), f'candidate postbuild non-build changes: {nonbuild(postbuild_delta)}'
parent_delta=differences(parent,parent_saved)
assert not nonbuild(parent_delta), f'R360 parent non-build changes since saved baseline: {nonbuild(parent_delta)}'
clone_delta=differences(cand,parent)
assert nonbuild(clone_delta)==['NameMatcher.ml','llbc/LlbcAstUtils.ml'], nonbuild(clone_delta)
assert sha_file(SRC/'NameMatcher.ml')==EXPECTED['NameMatcher.ml']
assert sha_file(SRC/'llbc/LlbcAstUtils.ml')==EXPECTED['llbc/LlbcAstUtils.ml']
assert sha_file(SRC/'extract/ExtractTypes.ml')==EXPECTED['ExtractTypes.ml']
for rel,key in [('TranslateCore.ml','TranslateCore.ml'),('interp/InterpExpansion.ml','InterpExpansion.ml'),('PrePasses.ml','PrePasses.ml')]:
    assert sha_file(SRC/rel)==EXPECTED[key] and sha_file(PARENT_SRC/rel)==EXPECTED[key]
assert sha_file(PARENT_SRC/'NameMatcher.ml')==EXPECTED['R360_NameMatcher.ml']
assert sha_file(PARENT_SRC/'llbc/LlbcAstUtils.ml')==EXPECTED['R360_LlbcAstUtils.ml']
shared=regular_inodes(SRC)&regular_inodes(PARENT_SRC)
assert not shared, f'{len(shared)} shared regular-file inodes'
result=json.loads(BUILD_RESULT.read_text()); assert result['build_exit_status']==0 and result['binary_sha256']==EXPECTED['binary']
assert result['candidate_source_tree_sha256_before_build']==EXPECTED['prebuild_manifest'] or result['candidate_source_tree_sha256_before_build']=='ecba5557e6d92687aca0d2f89bb15426b88cdf5fceca25a27eca497c1d73fa37'
assert result['sampled_container_memory_swap_peak_bytes']==0
assert sha_file(CANDIDATE_BINARY)==EXPECTED['binary'] and sha_file(SRC/'_build/default/main.exe')==EXPECTED['binary']
inspect=json.loads(DOCKER_INSPECT.read_text()); assert len(inspect)==1
state=inspect[0]['State']; assert state['ExitCode']==0 and state['OOMKilled'] is False
samples=json.loads(CGROUP_SAMPLES.read_text())['samples']
mem_peaks=[int(s['memory.peak']) for s in samples if 'memory.peak' in s]
swap_peaks=[int(s['memory.swap.peak']) for s in samples if 'memory.swap.peak' in s]
assert mem_peaks and max(mem_peaks)<=7*1024**3
assert swap_peaks and max(swap_peaks)==0
for sample in samples:
    events=sample.get('memory.events','')
    if events:
        event_map={k:int(v) for k,v in (line.split() for line in events.splitlines())}
        assert event_map.get('oom',0)==0 and event_map.get('oom_kill',0)==0 and event_map.get('oom_group_kill',0)==0
binary_size=CANDIDATE_BINARY.stat().st_size
finished=datetime.now(timezone.utc).isoformat(timespec='microseconds')
OUT=BUILD_AUDIT/'postbuild-source-audit'
assert not OUT.exists(), f'refusing to overwrite {OUT}'
OUT.mkdir(mode=0o755)
(OUT/'candidate-current-manifest.json').write_text(json.dumps(cand,indent=2)+'\n')
(OUT/'R360-parent-current-manifest.json').write_text(json.dumps(parent,indent=2)+'\n')
(OUT/'candidate-prebuild-manifest.json').write_bytes(pre_bytes)
(OUT/'R360-parent-saved-postbuild-manifest.json').write_bytes(parent_bytes)
report={
 'status':'R363 postbuild source/cache and saved build evidence audit passed; no translation or semantics claim',
 'started_at_utc':started,'finished_at_utc':finished,'captured_at_unix_ns':time.time_ns(),
 'candidate_root':str(ROOT),'parent_R360_root':str(PARENT),
 'candidate_prebuild_manifest_sha256':sha_bytes(pre_bytes),'R360_parent_saved_postbuild_manifest_sha256':sha_bytes(parent_bytes),'clone_audit_sha256':sha_bytes(clone_bytes),
 'candidate_current_manifest_sha256':sha_bytes((OUT/'candidate-current-manifest.json').read_bytes()),'R360_parent_current_manifest_sha256':sha_bytes((OUT/'R360-parent-current-manifest.json').read_bytes()),
 'candidate_prebuild_to_postbuild_changed_path_count':len(postbuild_delta),'candidate_prebuild_to_postbuild_changed_paths':postbuild_delta,'all_candidate_changes_confined_to__build':not nonbuild(postbuild_delta),
 'R360_parent_current_to_saved_changed_paths':parent_delta,'R360_parent_nonbuild_unchanged':not nonbuild(parent_delta),
 'candidate_vs_R360_parent_nonbuild_changed_paths':nonbuild(clone_delta),'approved_source_changes_exact':nonbuild(clone_delta)==['NameMatcher.ml','llbc/LlbcAstUtils.ml'],
 'candidate_vs_parent_total_changed_path_count':len(clone_delta),'candidate_vs_parent_build_cache_changed_path_count':len([p for p in clone_delta if p=='_build' or p.startswith('_build/')]),
 'source_sha256':{rel:sha_file(SRC/rel) for rel in ('NameMatcher.ml','llbc/LlbcAstUtils.ml','extract/ExtractTypes.ml','TranslateCore.ml','interp/InterpExpansion.ml','PrePasses.ml')},
 'parent_R360_approved_base_hashes':{'NameMatcher.ml':sha_file(PARENT_SRC/'NameMatcher.ml'),'llbc/LlbcAstUtils.ml':sha_file(PARENT_SRC/'llbc/LlbcAstUtils.ml')},
 'shared_regular_file_inode_count':len(shared),
 'build':{'exit_status':result['build_exit_status'],'launch_revision':result['launch_revision'],'source_revision':result['source_revision'],'image_id':result['docker_image_id'],'binary_sha256':sha_file(CANDIDATE_BINARY),'binary_size_bytes':binary_size,'docker_OOMKilled':state['OOMKilled'],'container_cgroup_sample_count':len(samples),'container_memory_peak_bytes':max(mem_peaks),'container_swap_peak_bytes':max(swap_peaks),'oom_event_counters_all_zero':True,'no_translation_or_Lean_compile':result['translation_or_Lean_compile_run'] is False},
 'limitations':'This is a filesystem/build receipt audit only; it does not establish that the compiler overlay is semantically correct.'
}
(OUT/'audit.json').write_text(json.dumps(report,indent=2)+'\n')
checks=[]
for p in sorted(OUT.iterdir()):
    if p.is_file() and p.name!='SHA256SUMS': checks.append(f'{sha_file(p)}  {p.name}')
(OUT/'SHA256SUMS').write_text('\n'.join(checks)+'\n')
print(json.dumps({'audit_dir':str(OUT),'report':report,'SHA256SUMS_sha256':sha_file(OUT/'SHA256SUMS')},indent=2))
