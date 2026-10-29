"""Read-only own-2' rejection certificate: allocator-owned vs OTHER state.

No compilers, root-function executions, debugger attaches or host mutations.
A witnessed OTHER read refutes the complete-cone qualification condition;
this is deliberately not a positive whole-cone purity prover.
"""
from pathlib import Path
import hashlib, json, re, subprocess, time

R = Path(__file__).resolve().parents[2]
E = R / 'evidence/pv-ownf-20261029'
assert R == Path('/Users/dominic/ZK/.worktrees/pv-own')
assert subprocess.check_output(['git','branch','--show-current'],text=True).strip() == 'codex/pv-ownf-20261029'
prior_path = R / 'evidence/pv-owne-20261029/static-capture.json'
prior_raw = prior_path.read_bytes()
prior = json.loads(prior_raw)
for row in prior['sources']:
    assert hashlib.sha256(row['text'].encode()).hexdigest() == row['sha256']
    if 'git_blob' in row:
        b = subprocess.check_output(['git','show','HEAD:'+row['relative_path']])
        assert hashlib.sha256(b).hexdigest() == row['sha256'], row['relative_path']
records = [{k:s[k] for k in ['path','relative_path','size','sha256']} for s in prior['sources']]
remote = r'''
from pathlib import Path
import hashlib,json,subprocess,time
records=json.loads(RECORDS)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
for s in records:
 assert sha(s['path'])==s['sha256'],s['path']
 assert Path(s['path']).stat().st_size==s['size']
lib='/lib/x86_64-linux-gnu/libc.so.6'
client='/home/dombarker/project-offloads/codex-pv-rdea-20261028/client-deployed-baseline'
assert sha(lib)=='3a15d66867d83762c7f2f1e37359cb8f6c5743edb369c65285cb0b1c4f7498bf'
assert sha(client)=='fa888460b2c37bee087afd6289cd55219fe2732ea1e1c75011147ed15c260348'
commands={}
for name,cmd in [
 ('malloc',['objdump','-d','--disassemble=__libc_malloc',lib]),
 ('realloc',['objdump','-d','--disassemble=__libc_realloc',lib]),
 ('free',['objdump','-d','--disassemble=__libc_free',lib]),
 ('errno_location',['objdump','-d','--disassemble=__errno_location',lib]),
 ('pthread_create',['objdump','-d','--disassemble=pthread_create',lib]),
 ('symbols',['objdump','-T',lib]),
 ('sections',['readelf','-SW',lib]),
 ('notes',['readelf','-n',lib]),
 ('rustc',['/home/dombarker/.cargo/bin/rustc','+1.94.1','-Vv']),
 ('glibc',['getconf','GNU_LIBC_VERSION']),
]:
 r=subprocess.run(cmd,capture_output=True,text=True)
 assert r.returncode==0,(name,r.stderr)
 commands[name]=dict(command=cmd,exit=r.returncode,stdout=r.stdout,stderr=r.stderr)
headers=[]
for path in ['/usr/include/x86_64-linux-gnu/sys/single_threaded.h','/usr/include/errno.h','/usr/include/x86_64-linux-gnu/bits/errno.h']:
 b=Path(path).read_bytes();headers.append(dict(path=path,sha256=hashlib.sha256(b).hexdigest(),size=len(b),text=b.decode()))
print(json.dumps(dict(checked_at=time.time(),sources=records,commands=commands,headers=headers,binaries=[dict(path=p,sha256=sha(p),size=Path(p).stat().st_size)for p in [lib,client]])))
'''.replace('RECORDS',repr(json.dumps(records)))
start=time.monotonic()
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=remote,text=True,capture_output=True)
assert r.returncode==0,r.stderr
j=json.loads(r.stdout)
c={k:v['stdout'] for k,v in j['commands'].items()}
# The two old witnesses are now explicitly ALLOCATOR-INTERNAL.
assert re.search(r'ad764:.*20b188',c['malloc'])
assert re.search(r'ad79a:.*%fs:',c['malloc'])
# OTHER: mutable process-wide threading flag and nonallocator writer.
assert re.search(r'ad7b5:.*20c040.*__libc_single_threaded',c['malloc'])
assert re.search(r'9d336:.*movb.*20c040.*__libc_single_threaded',c['pthread_create'])
assert re.search(r'000000000020c040.*DO .bss.*__libc_single_threaded',c['symbols'])
assert 'only\n   thread in the process image' in j['headers'][0]['text']
# OTHER: incoming errno TLS, preserved by free. Both load the SAME TLS-offset slot.
assert re.search(r'ade4e:.*203df8',c['free'])
assert re.search(r'ade59:.*mov.*%fs:\(%rbx\),%r12d',c['free'])
assert re.search(r'adeae:.*mov.*%r12d,%fs:\(%rbx\)',c['free'])
assert re.search(r'2a6e4:.*203df8',c['errno_location'])
assert re.search(r'2a6eb:.*%fs:',c['errno_location'])
assert '__errno_location' in j['headers'][1]['text']
# Concrete user source follows both roots to mandatory first alloc.
texts={s['relative_path']:s['text']for s in prior['sources']}
tree=texts['crates/aspis-statement/src/pool_v1/pair_tree_hiding.rs']
forest=texts['crates/aspis-statement/src/pool_v1/pair_forest_hiding.rs']
assert 'Vec::with_capacity(POOL_V1_PAIR_COPY_ROW_LINKS_V1)' in tree
assert 'POOL_V1_PAIR_COPY_ROW_LINKS_V1: usize = 127' in tree
assert 'let mut links = build_pool_v1_pair_copy_row_schedule_v1()?' in forest
assert 'let mut rows = build_pool_v1_pair_forest_copy_row_schedule_v1()?' in forest
assert 'for row in pool_v1_pair_forest_copy_active_rows_v1()?' in forest
assert 'libc::malloc(layout.size())' in texts['std/src/sys/alloc/unix.rs']
assert 'libc::free(ptr as *mut libc::c_void)' in texts['std/src/sys/alloc/unix.rs']
j.update(
 checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 branch='codex/pv-ownf-20261029',
 worktree=str(R),
 source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
 prior_capture=dict(path=str(prior_path.relative_to(R)),sha256=hashlib.sha256(prior_raw).hexdigest()),
 classification='own-2′ qualification REJECTED: OTHER process/thread state; own-1 retained',
 readonly_inspection=dict(exit=0,wall_seconds=time.monotonic()-start,peak_rss='N/A (no formal/native execution result)',swap='N/A',print_axioms='N/A; no Lean declarations'),
 lean_attempts=0,native_scopes=0,kani_runs=0,artifact_executed=False,
 external_reads=[
  dict(instruction='malloc 0xad764',state='malloc initialization byte 0x20b188',classification='ALLOCATOR-INTERNAL; newly permitted by own-2′'),
  dict(instruction='malloc 0xad79a',state='tcache allocator TLS',classification='ALLOCATOR-INTERNAL; newly permitted by own-2′'),
  dict(instruction='malloc 0xad7b5',state='__libc_single_threaded 0x20c040',classification='OTHER',reason='Process-wide thread-count optimization flag, exported in sys/single_threaded.h, writable by pthread_create at 0x9d336 outside allocator entry points'),
  dict(instruction='free 0xade59',state='incoming errno TLS, through offset slot 0x203df8',classification='OTHER',reason='Same TLS location returned by __errno_location; general per-thread error state, saved and restored across successful free at 0xadeae, not allocator-owned state'),
  dict(instruction='std rust_oom HOOK.load',state='allocation failure handler',classification='FAILURE-ONLY retained under rdea-1; no success-path exemption or new trust item asserted'),
 ],
 limitation='Negative certificate; no exhaustive enumeration of all transitive libc internals, no positive purity/address-independence certificate. Remaining cone need not be certified after a witnessed OTHER read; no claim that these reads change returned values or leak witness data.')
E.mkdir(exist_ok=True)
(E/'static-capture.json').write_text(json.dumps(j,indent=2)+'\n')
print(json.dumps(dict(ok=True,classification=j['classification'],sources=len(records),reads=j['external_reads'],wall=j['readonly_inspection']['wall_seconds']),indent=2))
