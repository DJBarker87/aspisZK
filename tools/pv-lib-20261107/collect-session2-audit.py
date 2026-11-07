"""Collect one completed strict audit; never relaunch it."""
import hashlib,json,lzma,pathlib,shlex,subprocess
E=pathlib.Path('evidence/pv-lib-20261107');H='/home/dombarker/project-offloads/codex-pv-lib-20261107'
expected=json.loads((E/'SESSION2_AUDIT_ROOTS.json').read_text())['roots']
out=(E/'out-49481.log').read_text()
results=[json.loads(line.split('NEP62_RESULT ',1)[1]) for line in out.splitlines() if line.startswith('NEP62_RESULT ')]
assert len(results)==len(expected) and {r['root'] for r in results}==set(expected)
assert all(r['equal'] for r in results)
assert all(set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'} for r in results)
receipt=json.loads((E/'receipt-49481.json').read_text());assert receipt['accepted']
summary=dict(attempt=49481,strict_raw=True,root_count=len(results),unresolved=0,
    summary_mismatches=0,roots=results,receipt=receipt,
    qualification='Unchanged NEP private importAll walker; unresolved is a hard error. Only the new PLIB roots; no frozen-manifest replay.')
(E/'SESSION2_RAW_AUDIT.json').write_text(json.dumps(summary,indent=2)+'\n')
code=r'''
import pathlib,hashlib,json,lzma
p=pathlib.Path('/home/dombarker/project-offloads/codex-pv-lib-20261107/evidence/raw-audit')
roots=['PV_LIB_Arc124.installed', 'PV_LIB_Arc124.internal_reached', 'PV_LIB_Arc124Allocated.reached', 'PV_LIB_Arc124Counts.certified', 'PV_LIB_ArcClone360.certified', 'PV_LIB_Atomic121.certified', 'PV_LIB_Atomic121.returned_value', 'PV_LIB_Box443.installed', 'PV_LIB_Box443.internal_reached', 'PV_LIB_Box458.certified', 'PV_LIB_Box458.installed', 'PV_LIB_Box458.internal_reached', 'PV_LIB_Box537.installed', 'PV_LIB_Box537.internal_reached', 'PV_LIB_BoxNew.certified', 'PV_LIB_Clone214.certified', 'PV_LIB_Drop.certified', 'PV_LIB_NativeGraph.certified', 'PV_LIB_Registry.certified', 'PV_LIB_RootNative.certified171', 'PV_LIB_RootNative.certified268', 'PV_LIB_RootNative.certified3', 'PV_LIB_RootNative.certified4', 'PV_LIB_ScopeNative.certified14', 'PV_LIB_ScopeNative.certified165', 'PV_LIB_ScopeNative.certified168', 'PV_LIB_ScopeNative.certified269', 'PV_LIB_ScopeNative.certified271', 'PV_LIB_ScopeNative.certified7', 'PV_LIB_ScopeNative.certified8', 'PV_LIB_SliceAlloc47.certified', 'PV_LIB_SliceAlloc48.certified', 'PV_LIB_SliceAlloc59.certified', 'PV_LIB_SliceAllocNative.certified_f36', 'PV_LIB_SliceAllocNative.certified_f37', 'PV_LIB_SliceAllocNative.certified_f38', 'PV_LIB_SliceAllocNative.certified_f46', 'PV_LIB_SliceAllocNative.certified_f62', 'PV_LIB_SliceAllocators.certified64', 'PV_LIB_SliceAllocators.certified65', 'PV_LIB_SliceBuiltinNative.certified_arrayRepeat', 'PV_LIB_SliceBuiltinNative.certified_arrayToSliceMut', 'PV_LIB_SliceBuiltinNative.certified_arrayToSliceShared', 'PV_LIB_SliceBuiltinNative.certified_indexMut', 'PV_LIB_SliceCopy.certified', 'PV_LIB_SliceCtor31.certified', 'PV_LIB_SliceCtor35.certified', 'PV_LIB_SliceDrop.certified', 'PV_LIB_SliceLoopNative.certified_f10', 'PV_LIB_SliceLoopNative.certified_f16', 'PV_LIB_SliceLoopNative.certified_f17', 'PV_LIB_SliceLoopNative.certified_f18', 'PV_LIB_SliceLoopNative.certified_f20', 'PV_LIB_SliceNativeGraph.internalModel', 'PV_LIB_SliceNativeGraph.model', 'PV_LIB_SliceNoAlloc.certified', 'PV_LIB_SlicePtrParts.certifiedMut', 'PV_LIB_SlicePtrParts.certifiedShared', 'PV_LIB_SourceStoreComparison.cell_gap', 'PV_LIB_SourceStoreComparison.public_gap', 'PV_LIB_SourceStoreComparison.running_cell', 'PV_LIB_SpawnNative.certified213', 'PV_LIB_SpawnNative.certified295', 'PV_LIB_SpawnNative.certified452', 'PV_LIB_SpawnNative.certified453', 'PV_LIB_SpawnNative.certified454', 'PV_LIB_SpawnNative.certified455', 'PV_LIB_SpawnNative.certified456', 'PV_LIB_SpawnNative.certified457', 'PV_LIB_SpawnNative.certified459', 'PV_LIB_ThreadNamed.certified123', 'PV_LIB_ThreadNamed.certified18', 'PV_LIB_ThreadNamed.certified468', 'PV_LIB_ThreadNamed.certified469', 'PV_LIB_TlsNative.certified11', 'PV_LIB_TlsNative.certified122', 'PV_LIB_TlsNative.certified127', 'PV_LIB_TlsNative.certified128', 'PV_LIB_TlsNative.certified129', 'PV_LIB_TlsNative.certified130', 'PV_LIB_TlsNative.certified319', 'PV_LIB_TlsNative.certified410']
files=[q for q in p.iterdir() if q.is_file() and any(q.name.startswith('NEP_pv-thread_'+root+'_') for root in roots)]
manifest=[dict(name=q.name,bytes=q.stat().st_size,sha256=hashlib.sha256(q.read_bytes()).hexdigest()) for q in files]
payload={q.name:q.read_text() for q in files if q.suffix in ['.txt','.json']}
raw=json.dumps(payload,sort_keys=True).encode()
dest=p.parent/'SESSION2_RAW_GRAPH_ARCHIVE.json.xz';dest.write_bytes(lzma.compress(raw))
print(json.dumps(dict(files=manifest,archive_sha256=hashlib.sha256(dest.read_bytes()).hexdigest(),uncompressed_sha256=hashlib.sha256(raw).hexdigest(),archive_bytes=dest.stat().st_size)))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],text=True,capture_output=True)
assert r.returncode==0,r.stderr
manifest=json.loads(r.stdout);(E/'SESSION2_RAW_GRAPH_MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
r=subprocess.run(['scp','dombarker@100.108.41.90:'+H+'/evidence/SESSION2_RAW_GRAPH_ARCHIVE.json.xz',str(E/'SESSION2_RAW_GRAPH_ARCHIVE.json.xz')],capture_output=True)
assert r.returncode==0,r.stderr
raw=(E/'SESSION2_RAW_GRAPH_ARCHIVE.json.xz').read_bytes();assert hashlib.sha256(raw).hexdigest()==manifest['archive_sha256']
(E/'SESSION2_RAW_GRAPH_ARCHIVE.json.sha256').write_text(manifest['uncompressed_sha256']+'\n')
print('Strict raw audit:',len(results),'roots; graph archive bytes',len(raw))
