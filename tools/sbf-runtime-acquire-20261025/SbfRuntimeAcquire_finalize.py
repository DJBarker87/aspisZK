"""Local evidence index and source-only next integration artifact. No host call."""
import ast,hashlib,json,pathlib,resource,subprocess,sys,time
START=time.monotonic();ROOT=pathlib.Path(__file__).resolve().parents[2];HERE=pathlib.Path(__file__).resolve().parent;OUT=ROOT/'evidence/sbf-runtime-acquire-20261025'
def pin(b):return dict(size=len(b),sha256=hashlib.sha256(b).hexdigest())
def save(name,d):
 b=(json.dumps(d,indent=2,sort_keys=True)+'\n').encode();assert len(b)<=5_000_000;(OUT/name).write_bytes(b)
def load(name):return json.loads((OUT/name).read_bytes())
producer={};statements={}
for name in ('SbfProducer_package.py','SbfProducer_pins.py','SbfProducer_continue.py','SbfProducer_backend_candidate.py','SbfProducerLinux_capture.py','SbfProducer_entry.py','SbfProducer_user_entry.py','DEPLOYMENT-REVIEW.md'):
 path='tools/sbf-producer-20261025/'+name;b=subprocess.check_output(['git','show','20a0f5bb38:'+path],cwd=ROOT);producer['20a0f5bb38:'+path]=pin(b)
 if name.endswith('.py'):
  tree=ast.parse(b);lines=b.decode().splitlines(keepends=True)
  for n in tree.body:
   if isinstance(n,ast.FunctionDef) and n.name in {'approval','producer_fixed_body','fixed_backend_body','validate_runtime'}:statements[name+':'+n.name]=''.join(lines[n.lineno-1:n.end_lineno])
plan=load('SbfRuntimeAcquire-plan.json');candidate=load('SbfRuntimeAcquire-candidate-INPUT-DATA-ONLY.json')
proposal=dict(status='SOURCE_ONLY_NEXT_ARTIFACT_FOR_LEAD_REVIEW; NOT IMPLEMENTED/EXECUTABLE/APPROVED',
 finite_candidate=pin((OUT/'SbfRuntimeAcquire-candidate-INPUT-DATA-ONLY.json').read_bytes()),candidate_status=candidate['status'],
 raw_data=pin((OUT/'SbfRuntimeAcquire-transport.stdout').read_bytes()),payload=load('SbfRuntimeAcquire-preregister.json')['payload'],plan=pin((OUT/'SbfRuntimeAcquire-plan.json').read_bytes()),
 producer_sources=producer,complete_source_statements=statements,
 actual_producer_path='root_continuation -> producer_fixed_body -> approval()[runtime] -> validate_runtime -> internal_backend',
 current_gates=['approval requires published exact RUNTIME_PIN dict; immutable RUNTIME_PIN=() rejects','installed entries disabled'],
 unused_gate='fixed_backend_body RUNTIME_APPROVAL global is not an additional producer_fixed_body path gate',
 reconciliation=[dict(field='schema',captured=plan['candidate_template']['version'],producer_approval='SbfProducer-runtime-v1 with schema/runtime/host/roles/scope_path/limits/env',required='Separate probe-specific schema/source; do not insert tiny manifest into approval or manufacture host/role closure'),
 dict(field='root',captured=plan['candidate_template']['root'],producer='/var/lib/SbfProducerSeal-20261025-v1/rootfs',required='Publish a new exact probe root and matching fixed layout/validator before any use; no silent rename'),
 dict(field='argv',captured=plan['candidate_template']['argv'],required='Pin complete postexec body/argv from reviewed probe source; separately reconcile Producer fixed body, no silent substitution'),
 dict(field='physical',captured='91 logical file candidates,82 physical file endpoints; source disk nofollow pins',producer='/opt/aspis/SbfProducer-20261025-v1/runtime/ prefix required by root_continuation',required='New exclusive-copy source-only installer specification plus exact mapping and new pins; never rename/chown/adopt user staging'),
 dict(field='environment',captured=plan['candidate_template']['env'],required='Publish exact env and reconcile at probe boundary; matching env alone establishes no runtime identity'),
 dict(field='limits/admission',captured='512MiB sampled read-only metadata exception; no cgroup',required='New explicit probe allocation/control/role/admission artifacts; current exception grants zero native/root budget')],
 required_concrete_artifacts=['fixed finite-probe source with exact own admission/roles/descriptor/stdio/lifecycle rules','literal runtime schema + complete root/argv/alias mapping and pinned source-only exclusive-copy installer','independent review of complete source/guard/capture delta and failure/cancellation behavior','explicit separate bounded native/root allocation before any execution; none requested now'],
 exclusive_copy_spec=['fresh absent root-owned nonwritable ancestry checked nofollow','root-only O_EXCL|O_NOFOLLOW writers create new regular single-link inodes','copy only reviewed pinned bytes, check source FD and ancestry stability, hash copied bytes, close all writers then seal444/555','aliases are individual clones and each copy counts toward64MiB/256rows; no symlink/writer adoption','retain partial failures; no signatures/runtime manifest approval inferred from incomplete host closure'],
 runtime_approval=None,producer_activation=False,installer_implemented=False,actual_rootfs=False,
 open_obligations=['historical openFD/inode binding','executed bytecode/native runtime effects','conditional imports/dlopen/locale/NSS','private guest/control/LSM/cancellation/parentdeath','full host roles/sudo/monitor/plugins/tools','SDK/std/runtime/allocator/extraction','cryptographic/adaptive-oracle/event-law joins; both deployed targets NOT ESTABLISHED'])
save('SbfRuntimeAcquire-NEXT-FINITE-PROBE-INTEGRATION.json',proposal)
# Failure overlays are immutable retained sources; later measurements cannot repair
# absent original failure metrics. Reference successful checker dependencies only.
for label in ('preflight','check'):
 name='SbfRuntimeAcquire-'+label+'-attempt1-failure.json';d=load(name)
 source=HERE/d['retained_source'];d['retained_source_pin']=pin(source.read_bytes());d['dependency_assessment']='same local Python environment as subsequent passing receipt; original failure metrics UNOBSERVED, not reconstructed'
 save(name,d)
usage=resource.getrusage(resource.RUSAGE_SELF)
files={str(p.relative_to(ROOT)):pin(p.read_bytes()) for folder in (HERE,OUT) for p in sorted(folder.iterdir()) if p.is_file() and p.name!='SbfRuntimeAcquire-artifact-index.json'}
save('SbfRuntimeAcquire-artifact-index.json',dict(command=getattr(sys,'orig_argv',sys.argv),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT).decode().strip(),source_overlay_and_artifacts=files,producer_immutable_sources=producer,exit=0,wall_seconds=time.monotonic()-START,peak_rss_bytes=usage.ru_maxrss*(1 if sys.platform=='darwin' else 1024),swap=usage.ru_nswap,dependencies={n:dict(path=m.__file__,**pin(pathlib.Path(m.__file__).read_bytes())) for n,m in sorted(sys.modules.items()) if getattr(m,'__file__',None) and pathlib.Path(m.__file__).is_file()},interpreter=dict(path=sys.executable,version=sys.version,**pin(pathlib.Path(sys.executable).read_bytes())),new_host_calls=0,axioms='N/A; data',derived_JSON_over5MB=[]))
print(json.dumps(dict(status='indexed',candidate=proposal['finite_candidate'],files=len(files),next='source-only finite probe reconciliation; lead review required')))
