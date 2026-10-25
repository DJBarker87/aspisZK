"""Fixed source-only handoff indexing. No operational imports or native effects."""
import hashlib,json,pathlib,resource,subprocess,sys,time
START=time.monotonic();H=pathlib.Path(__file__).resolve().parent;O=H.parents[1]/'evidence/sbf-finite-probe-20261025'
def pin(b):return dict(size=len(b),sha256=hashlib.sha256(b).hexdigest())
rev=subprocess.check_output(['git','rev-parse','HEAD']).decode().strip()
paths=subprocess.check_output(['git','diff','--name-only','86d9ae90c6..HEAD']).decode().splitlines()
assert all(p.startswith(('tools/sbf-finite-probe-20261025/','evidence/sbf-finite-probe-20261025/')) for p in paths)
tests=json.loads((O/'SbfFinite-tests-attempt8.json').read_bytes());audit=json.loads((O/'SbfFinite-final-check2.json').read_bytes())
# Source identity reuse only, no unchanged suite or identity gate re-executed.
for name,p in audit['source_overlay'].items():
 if name!='SbfFinite_REVIEW.md':assert pin((H/name).read_bytes())==p,(name,'post-audit source changed')
assert tests['exit']==audit['exit']==0 and tests['tests']==30
files={}
for folder in (H,O):
 for p in sorted(folder.iterdir()):
  if p.is_file() and p.name!='SbfFinite-HANDOFF.json':
   raw=p.read_bytes();assert not (p.suffix=='.json' and len(raw)>5_000_000)
   files[str(p.relative_to(H.parents[1]))]=pin(raw)
r=resource.getrusage(resource.RUSAGE_SELF);children=resource.getrusage(resource.RUSAGE_CHILDREN)
factor=1 if sys.platform=='darwin' else 1024
assert (r.ru_maxrss+children.ru_maxrss)*factor<512*2**20
report=dict(schema='SbfFinite-handoff-source-v1',status='COMPLETE_INTERNAL_AND_DORMANT_ENTRY_SOURCE; STOP_FOR_LEAD_REVIEW',
 branch='codex/cx-sbf-finite-probe-20261025',source_revision=rev,base='86d9ae90c6',
 command=getattr(sys,'orig_argv',sys.argv),exit=0,wall_seconds=time.monotonic()-START,
 peak_process_rss_bytes=r.ru_maxrss*factor,peak_aggregate_rss_bytes=None,
 aggregate_peak_upper_bound_bytes=(r.ru_maxrss+children.ru_maxrss)*factor,
 aggregate_method='exact concurrent peak UNOBSERVED; conservative self+serial-Git-child peak sum',swap=r.ru_nswap,child_swaps=children.ru_nswap,
 files=files,dependencies={n:dict(path=m.__file__,**pin(pathlib.Path(m.__file__).read_bytes())) for n,m in sorted(sys.modules.items()) if getattr(m,'__file__',None) and pathlib.Path(m.__file__).is_file()},
 interpreter=dict(path=sys.executable,version=sys.version,**pin(pathlib.Path(sys.executable).read_bytes())),
 axioms='N/A; source/text/hash/AST/synthetic only',
 validation=dict(new_synthetic_test_methods=30,tests='SbfFinite-tests-attempt8.json',source_checks=276,audit='SbfFinite-final-check2.json',source_revision_assessment='Current operative source byte-identical to pinned final receipts; reused validation, not a new identity or native gate'),
 all_actual_budgets=dict(host=0,SSH=0,network=0,host_metadata=0,native=0,root=0,sudo=0,namespace=0,compiler=0,Lean=0,Rust=0,Cargo=0,Kani=0,extraction=0,backend=0,ELF=0,probe=0,install=0),
 assumptions=dict(discharged='No formal/security assumptions discharged; finite source mechanisms and explicit synthetic behavior supplied',added='None to protocol/model/security contract; bootstrap authentication remains explicit and external',retained=['kernel/root','CPython/native/loader/tool/privilege','conditional imports/dlopen/locale/NSS','full host roles/controllers/LSM/pidfd permissions','SIGKILL/D-state/orphan/parentdeath','SDK/std/runtime/allocator/extraction','frozen SBF/compiler/artifact binding','cryptographic/adaptive oracle/event-law joins']),
 both_deployed_targets='NOT ESTABLISHED',
 next='Independent lead source/bootstrap/guard/capture/delta review; then separately publish finite operational data and deployment identity, allocate and authorize future bounded native/root work. No current permission question.',
 ELF_pins_unchanged=dict(default='f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4',devnet='63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299',Pool='121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548'),
 no_ELF_or_shipped_source_read_or_change=True,derived_JSON_over5MB=[])
raw=(json.dumps(report,sort_keys=True,indent=2)+'\n').encode();assert len(raw)<5_000_000
assert not (O/'SbfFinite-HANDOFF.json').exists()
(O/'SbfFinite-HANDOFF.json').write_bytes(raw)
print(json.dumps(dict(status=report['status'],source_revision=rev,files=len(files),wall_seconds=report['wall_seconds'],rss=report['peak_process_rss_bytes'],aggregate_upper_bound=report['aggregate_peak_upper_bound_bytes'])))
