"""Read-only own-2 rejection certificate; no compiler or artifact execution.

This is an auditable source/runtime capture with mandatory-path assertions,
not a general purity prover. A counterexample to the complete-cone condition
does not require proving purity of every remaining callee.
"""
from pathlib import Path
import hashlib, json, subprocess, re

R = Path(__file__).resolve().parents[2]
E = R / 'evidence/pv-owne-20261029'
H = 'dombarker@100.108.41.90'
assert R == Path('/Users/dominic/ZK/.worktrees/pv-own')
assert subprocess.check_output(['git', 'branch', '--show-current'], text=True).strip() == 'codex/pv-owne-20261029'
revision = subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip()
paths = [
 'alloc/src/vec/mod.rs', 'alloc/src/vec/into_iter.rs',
 'alloc/src/vec/spec_from_iter.rs', 'alloc/src/vec/spec_from_iter_nested.rs',
 'alloc/src/vec/in_place_collect.rs', 'alloc/src/vec/in_place_drop.rs',
 'alloc/src/vec/spec_extend.rs', 'alloc/src/vec/set_len_on_drop.rs',
 'alloc/src/raw_vec/mod.rs', 'alloc/src/alloc.rs',
 'core/src/iter/traits/iterator.rs', 'core/src/iter/adapters/filter.rs',
 'core/src/iter/adapters/flatten.rs', 'core/src/iter/adapters/map.rs',
 'core/src/iter/adapters/fuse.rs', 'core/src/iter/range.rs',
 'core/src/array/iter.rs', 'core/src/array/iter/iter_inner.rs',
 'core/src/slice/iter.rs', 'core/src/slice/iter/macros.rs',
 'core/src/slice/mod.rs', 'core/src/slice/sort/mod.rs',
 'core/src/slice/sort/unstable/mod.rs',
 'core/src/slice/sort/unstable/quicksort.rs',
 'core/src/slice/sort/unstable/heapsort.rs',
 'core/src/slice/sort/shared/mod.rs', 'core/src/slice/sort/shared/pivot.rs',
 'core/src/slice/sort/shared/smallsort.rs',
 'core/src/alloc/layout.rs', 'core/src/alloc/mod.rs',
 'core/src/ptr/mod.rs', 'core/src/ptr/non_null.rs',
 'core/src/cmp.rs', 'core/src/option.rs', 'core/src/result.rs',
 'std/src/alloc.rs', 'std/src/sys/alloc/mod.rs', 'std/src/sys/alloc/unix.rs',
]
application = [
 'crates/aspis-statement/src/pool_v1/pair_tree_hiding.rs',
 'crates/aspis-statement/src/pool_v1/pair_tree_profile.rs',
 'crates/aspis-statement/src/pool_v1/pair_forest_hiding.rs',
 'crates/aspis-prover/src/host_forest.rs',
 'tools/r1-cost-probe/Cargo.toml',
 'tools/r1-cost-probe/src/bin/devnet_spend.rs',
]
code = r'''
from pathlib import Path
import json,hashlib,subprocess
S=Path('/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library')
F=Path('/home/dombarker/project-offloads/codex-pv-fscan-20261028/src')
out={'sources':[], 'commands':[]}
for root,paths in [(S,STD_PATHS),(F,APP_PATHS)]:
 for rel in paths:
  p=root/rel;b=p.read_bytes()
  out['sources'].append(dict(path=str(p),relative_path=rel,size=len(b),sha256=hashlib.sha256(b).hexdigest(),text=b.decode()))
for cmd in [
 ['/home/dombarker/.cargo/bin/rustc','+1.94.1','-Vv'],
 ['getconf','GNU_LIBC_VERSION'],
 ['objdump','-d','--disassemble=__libc_malloc','/lib/x86_64-linux-gnu/libc.so.6'],
 ['objdump','-d','--start-address=0x89b90','--stop-address=0x89bd0','/home/dombarker/project-offloads/codex-pv-rdea-20261028/client-deployed-baseline'],
 ['objdump','-d','--start-address=0x1cdc20','--stop-address=0x1cdc90','/home/dombarker/project-offloads/codex-pv-rdea-20261028/client-deployed-baseline'],
 ['objdump','-T','/home/dombarker/project-offloads/codex-pv-rdea-20261028/client-deployed-baseline'],
 ['objdump','-d','--start-address=0xa9e60','--stop-address=0xa9ea0','/lib/x86_64-linux-gnu/libc.so.6'],
 ['readelf','-SW','/lib/x86_64-linux-gnu/libc.so.6'],
]:
 r=subprocess.run(cmd,capture_output=True,text=True)
 assert r.returncode==0,(cmd,r.stderr)
 out['commands'].append(dict(command=cmd,exit=r.returncode,stdout=r.stdout,stderr=r.stderr))
out['binaries']=[]
for p in [Path('/home/dombarker/project-offloads/codex-pv-rdea-20261028/client-deployed-baseline'),Path('/lib/x86_64-linux-gnu/libc.so.6')]:
 b=p.read_bytes();out['binaries'].append(dict(path=str(p),size=len(b),sha256=hashlib.sha256(b).hexdigest()))
for name,path in [('deployed_units','/home/dombarker/project-offloads/codex-pv-ownd-20261029/deployed-units.json'),('deployed_lock','/home/dombarker/project-offloads/codex-pv-ownd-20261029/deployed-client-Cargo.lock')]:
 p=Path(path);b=p.read_bytes();out[name]=dict(path=path,size=len(b),sha256=hashlib.sha256(b).hexdigest(),text=b.decode())
print(json.dumps(out))
'''.replace('STD_PATHS', repr(paths)).replace('APP_PATHS', repr(application))
r = subprocess.run(['ssh', H, 'python3', '-'], input=code, capture_output=True, text=True)
assert r.returncode == 0, r.stderr
j = json.loads(r.stdout)
for s in j['sources']:
 assert hashlib.sha256(s['text'].encode()).hexdigest() == s['sha256']
 if s['relative_path'] in application:
  b = subprocess.check_output(['git', 'show', 'HEAD:' + s['relative_path']])
  assert hashlib.sha256(b).hexdigest() == s['sha256'], s['relative_path']
  s['git_blob'] = subprocess.check_output(['git', 'rev-parse', 'HEAD:' + s['relative_path']], text=True).strip()
assert j['binaries'][0]['sha256'] == 'fa888460b2c37bee087afd6289cd55219fe2732ea1e1c75011147ed15c260348'
texts = {s['relative_path']:s['text'] for s in j['sources']}
assert 'Vec::with_capacity(POOL_V1_PAIR_COPY_ROW_LINKS_V1)' in texts[application[0]]
assert 'POOL_V1_PAIR_COPY_ROW_LINKS_V1: usize = 127' in texts[application[0]]
assert 'libc::malloc(layout.size())' in texts['std/src/sys/alloc/unix.rs']
assert 'System.alloc(layout)' in texts['std/src/alloc.rs']
assert 'HOOK.load(Ordering::Acquire)' in texts['std/src/alloc.rs']
malloc = j['commands'][2]['stdout']
assert re.search(r'ad79a:.*%fs:', malloc)
assert '20b188' in malloc
assert '__rdl_alloc' in j['commands'][3]['stdout']
assert 'malloc@GLIBC_2.2.5' in j['commands'][4]['stdout']
assert re.search(r'a9e7b:.*movb.*20b188', j['commands'][6]['stdout'])
assert '.bss' in j['commands'][7]['stdout']
j.update(source_revision=revision,classification='own-2 qualification REJECTED; supporting static/runtime inspection only',
 artifact_executed=False,compilers_started=0,lean_attempts=0,native_scopes=0,kani_runs=0,
 exact_external_reads=[
  dict(path='/lib/x86_64-linux-gnu/libc.so.6',symbol='__libc_malloc',address='0xad764',read='cmpb $0x0,0x15da1d(%rip): reads mutable allocator initialization state at ELF virtual address 0x20b188'),
  dict(path='/lib/x86_64-linux-gnu/libc.so.6',symbol='__libc_malloc',address='0xad79a',read='mov %fs:0x0(%r13),%rdx: reads thread-local allocator state on the initialized positive-size path'),
  dict(path='std/src/alloc.rs',symbol='rust_oom',read='HOOK.load(Ordering::Acquire); failure-only, separately retained under rdea-1, not the decisive success-path obstruction')],
 note='No positive complete-cone purity claim. The mandatory allocator edge falsifies the universal no-external-read condition before subsequent stages. No witness-dependent leak is claimed.')
E.mkdir(exist_ok=True)
(E/'static-capture.json').write_text(json.dumps(j,indent=2)+'\n')
print(json.dumps(dict(ok=True,sources=len(j['sources']),bytes=(E/'static-capture.json').stat().st_size,reads=j['exact_external_reads']),indent=2))
