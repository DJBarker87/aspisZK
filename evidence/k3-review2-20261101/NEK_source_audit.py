"""Expand recorded sources and audit harness storage, without replaying unaffected work."""
from NEK_scan import *
from NEK_recover import recover
from NEK_host import py
A=read_json(ROOT/'evidence/k3-audit-20261030/NEH_APPLICABILITY.json');index={r['receipt']:r for r in A['receipts']}
C=read_json(E/'NEK_CLOSURE.json');wanted={k['receipt'] for row in C['rows'] for k in row['closure']['kani']}
# Scan source-pinned frozen Rust: declaration storage vs lifetime syntax is explicit.
frozen_names=subprocess.check_output(['git','ls-tree','-r','--name-only',FROZEN],text=True).splitlines()
mutable=[];interior=[]
for n in frozen_names:
 if not(n.startswith(('crates/','programs/')) and n.endswith('.rs')):continue
 t=frozen(n).decode()
 if re.search(r'\bstatic\s+mut\b',t):mutable.append(n)
 if re.search(r'\bstatic\s+\w+\s*:[^;=]*(?:Atomic|UnsafeCell|RefCell|Cell\s*<)',t):interior.append(n)
(E/'NEK_FROZEN_STORAGE.json').write_text(json.dumps(dict(revision=FROZEN,mutable_static_files=mutable,interior_mutable_static_files=interior,limitation='frozen Rust source inventory; external dependency/tool/macro trust retained'),indent=2)+'\n')
results=[]
for rp in sorted(wanted):
 old=index.get(rp)
 if not old:results.append(dict(receipt=rp,status='UNREVIEWED',reason='not in NEH selected inventory'));continue
 # Keep existing restored results; no new replay or source claim.
 if any(k['receipt']==rp and k['outcome']=='RESTORED' for row in C['rows'] for k in row['closure']['kani']):
  results.append(dict(receipt=rp,status='REUSED_RESTORED',reason='NEH same-name local-record property/control evidence retained'));continue
 try:o,missing=recover(rp)
 except Exception as ex:results.append(dict(receipt=rp,status='OPEN',reason=str(ex)));continue
 writes=[dict(source=n,line=i+1,text=l.strip()) for n,t in o.items() for i,l in enumerate(t.splitlines()) if re.search(r'\bstatic\s+mut\b|\bstatic\s+\w+\s*:[^;=]*(?:Atomic|UnsafeCell|RefCell|Cell\s*<)',l)]
 includes=[dict(source=n,path=p) for n,t in o.items() for p in re.findall(r'(?:include!\s*\(|#\[path\s*=\s*)"([^"]+)"',t)]
 macros=[dict(source=n,name=m) for n,t in o.items() for m in re.findall(r'\bmacro_rules!\s*(\w+)',t)]
 # The storage audit is narrower than macro exclusion: unresolved macro-generated
 # storage remains OPEN. Builtin derives, Kani instrumentation, pinned KMX copy
 # includes and existing frozen Rust macros carry the same retained tool trust.
 unknown=[m for m in macros if m['name'] not in ['parts_store']]
 result=dict(receipt=rp,recovered_sources={n:sha(t.encode()) for n,t in o.items()},unresolved=missing,writable_static_sites=writes,includes=includes,macro_definitions=macros,status='OPEN',reason='source audit requires explicit closure review')
 if writes:result['reason']='written-static module remains suspended; local-context migration required'
 elif missing:result['reason']='exact receipt-pinned source unavailable'
 elif not unknown:result.update(status='STORAGE_FREE_RECORDED_CLOSURE',reason='all receipt-pinned Rust inputs recovered; no writable-static declaration; includes/macros listed for expansion audit, external tool/runtime trust retained')
 results.append(result)
(E/'NEK_SOURCE_AUDIT.json').write_text(json.dumps(results,indent=2)+'\n')
print(json.dumps(collections.Counter(r['status'] for r in results)))
