#!/usr/bin/env python3
"""Generate reviewable future commands; deliberately cannot launch a gate."""
import copy,hashlib,json,pathlib,resource,subprocess,time
T=pathlib.Path(__file__).resolve().parent;E=T.parents[1]/'evidence/sbf-recapture-prep-20261024';start=time.monotonic()
BASE='009b61e61bf52dba92c4fbefae79702a938f05b3'
p='evidence/sbf-identity-20261024/recapture-plan.json'
b=subprocess.check_output(['git','show',BASE+':'+p]);old=json.loads(b);new='/home/dombarker/project-offloads/codex-cx-sbf-recapture-20261024'
def remap(x):
 if isinstance(x,str):return x.replace(old['stage'],new).replace('--unit=sbf-identity-20261024-','--unit=sbf-recapture-20261024-')
 if isinstance(x,list):return [remap(v) for v in x]
 if isinstance(x,dict):return {k:remap(v) for k,v in x.items()}
 return x
plan=remap(old)
for a,z in zip(old['builds'],plan['builds']):
 # Historical receipts retain original spelling and identity, without rewriting.
 z['historical_predecessor']=copy.deepcopy(a['historical_predecessor'])
 assert z['expected_sha256']==a['expected_sha256']
 z['status']='PREPARED NOT RUN; BLOCKED for execution'
plan.update(schema='SbfRecapturePrep-plan-v1',status='PREPARED NOT RUN; execution disabled pending separate lead allocation and unresolved gates',reviewed_plan=dict(revision=BASE,path=p,sha256=hashlib.sha256(b).hexdigest()),builds_run=0,headroom='UNKNOWN; ResourceSLAB/GO candidate NOT ADOPTED',execution_blockers=['Donor visibility denied; no complete cache provenance/inventory/export or freshness assessment','Cold compilation guard not validated before dependency/compiler/build-script execution','Registry archives AND unpacked consumed source bytes not verified against frozen lock','Time-of-use exclusion and complete effective input closure unestablished','Current approved strict admission runner/pin not supplied; no admission or scope launched','Separate lead allocation required'])
plan['pre_go_post_required']={
 'phases':['pre after private source/cache preparation','go inside reviewed admission and concurrency exclusion immediately before invocation','post before releasing exclusion'],
 'inputs':['entire 7978-file source incl config/build scripts/target/lock + exclusion policy','immutable transparent diagnostics wrapper','cargo-build-sbf and SDK dispatch configuration','rustup proxy/link chain/selected host cargo/rustc/compiler runtime/sysroots/build-script compiler/linker','SBF rustc/compiler driver/LLVM/linker/objcopy/runtime/newlib/all target archives/full rust-src','registry archive checksums from Cargo.lock AND every unpacked consumed source byte/config','all copied target constituents including .fingerprint dep-info outputs build-script artifacts','exact environment allowlist only; start from env -i, explicitly review HOME/tool selection/locale/temp requirements; no secret environment dump'],
 'check':'Digest/size/type/mode/link-path equality plus actual invocation/library path capture. Unmanifested input, change, or ambiguous writer denies. Snapshots alone do not prove time-of-use identity.'}
plan['diagnostic_freshness']={
 'status':'PROPOSED; no mtimes/fingerprints invalidated in this job',
 'selected_crates':['aspis_core','aspis_statement','aspis_r1_cost_probe','aspis_r1_cost_probe_program','aspis_pool'],
 'method':'In own materialized src only, hash selected crates input closure, advance owned .rs mtimes after copy; retain identical before/after content and mtime receipt. Do not clean or edit fingerprints. Capture fresh empty per-mode diagnostics, require selected crate command/mono/MIR/LLVM files created after go and exact target,opt3,compiler/owned source paths. Do not count preexisting copied files as newly emitted. Preserve default before devnet.',
 'limitations':'Source relocation, new wrapper path, build-script OUT_DIR/provenance, host-tool/runtime/config and default/devnet env transitions may invalidate dependency fingerprints. mtime forcing alone cannot prove new diagnostics or warm dependencies.'}
plan['cold_guard']={
 'status':'BLOCKED; design only, not installed or run',
 'requirement':'Deny unexpected dependency compiler or build-script execution BEFORE it starts; offline/locked/-j4/timeout/memory cap do not provide this guarantee.',
 'candidate':'An outer invocation dispatcher could allow metadata queries and selected owned crate compile commands then delegate verbatim to the unchanged pinned wrapper; reject any dependency or unapproved build-script command before exec.',
 'assessment':'Changing RUSTC_WRAPPER/RUSTC or adding RUSTC_WORKSPACE_WRAPPER can change Cargo fingerprints/unit identity. The dispatcher may itself force dependencies dirty. Without donor fingerprints and a validated same-identity interception mechanism, do not call it warm, launch it, or fall back to cold compilation. A monitor of Cargo logs or polling processes is too late.',
 'next':'Lead obtains permission-complete donor quiescence and exact source/tool/dependency/fingerprint assessment; separately review a pre-exec guard plus build-script coverage. No guard contents or Cargo fingerprints fabricated.'}
plan['resources']={ 'scope':'sequential MemoryHigh=6G MemoryMax=8G MemorySwapMax=0 TasksMax=64; retain stricter existing 5G/7G', 'admission':'approved strict finite disjoint populated reservations including proposed 8GiB <55GiB, exclusive uncapped/resident/MemAvailable and 7GiB control-reserve gates; missing/raced data deny; no slab credit', 'smaller_gate':'No 2GiB proposal recommended while cold guard/cache freshness unestablished. Historical warm ~1.18GB peaks are reused only; lead decides separately.', 'scope_launches':0 }
(E/'future-plan.json').write_text(json.dumps(plan,indent=2)+'\n')
u=resource.getrusage(0);c=resource.getrusage(resource.RUSAGE_CHILDREN)
(E/'plan.receipt.json').write_text(json.dumps(dict(command=['python3',str(T/'SbfRecapturePrep_plan.py')],exit=0,wall_seconds=time.monotonic()-start,peak_rss_bytes=u.ru_maxrss,children_peak_rss_bytes=c.ru_maxrss,swaps=u.ru_nswap+c.ru_nswap,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),script_sha256=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),reviewed_plan_sha256=hashlib.sha256(b).hexdigest(),print_axioms='N/A'),indent=2)+'\n')
print('Prepared three exact relocated commands; execution disabled; no gate run.')
