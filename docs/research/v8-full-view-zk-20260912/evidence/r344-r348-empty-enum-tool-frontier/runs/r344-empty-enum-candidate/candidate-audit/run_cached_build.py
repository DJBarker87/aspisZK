# LAUNCH-CAPABLE RUNNER. Do not execute without lead's explicit build-launch authorization.
import pathlib,hashlib,json,subprocess,time,os
root=pathlib.Path("/home/dombarker/project-offloads/aspis-r344-direct-empty-enum-candidate-20261002-a"); src=root/'src'; audit=root/'candidate-audit'; parent=pathlib.Path("/home/dombarker/project-offloads/aspis-r312-slice-length-candidate-20261002-a")
sha=lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
assert src.is_dir() and (src/'_build/default/main.exe').is_file()
assert not (root/'aeneas-r344-direct-empty-enum-candidate').exists()
assert sha(src/'interp/InterpExpansion.ml')=="da68f59bc0240bad9862f0733aecd7265c239dbe988669d5d8ddddafc5a79b19",sha(src/'interp/InterpExpansion.ml')
assert sha(parent/'aeneas-r312-slice-length-candidate')=="fff3717072567f291fc1444f52a3dc7c1f8ba4ddc5c3980e94c863cdceb60f4f",sha(parent/'aeneas-r312-slice-length-candidate')
image=subprocess.check_output(['docker','image','inspect','ef96e46342a4','--format','{{.Id}} {{.Size}}'],text=True).strip()
assert image.startswith('sha256:ef96e46342a4159b6a62663e1ff5474a5f5deaf260daf08ea7b0963974418db7 '),image
mem=lambda:{k:v for k,v in (l.split(':',1) for l in pathlib.Path('/proc/meminfo').read_text().splitlines()) if k in ('MemTotal','MemAvailable','SwapTotal','SwapFree')}
before=mem(); avail=int(before['MemAvailable'].split()[0]); assert avail>=24*1024*1024,before
r312=subprocess.check_output(['systemctl','show','aspisr312.slice','-p','MemoryHigh','-p','MemoryMax','-p','MemorySwapMax','-p','MemoryCurrent'],text=True)
active=subprocess.check_output(['systemctl','--user','list-units','--type=service','--state=running','--no-legend'],text=True)
docker_before=subprocess.check_output(['docker','ps','--no-trunc','--format','{{.ID}} {{.Names}} {{.Status}}'],text=True)
pre={'meminfo_before':before,'available_kib':avail,'existing_r312_parent_slice':r312,'active_user_services':active,'active_docker_containers':docker_before,'docker_image_inspect':image,'systemd_caps':{'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':'0','TasksMax':128},'docker_caps':{'memory_reservation':'5g','memory':'7g','memory-swap':'7g (equal to memory; no swap)','pids_limit':128,'network':'none','cgroup-parent':'aspisr344.slice'},'planned_r312_plus_r344_maximum':'14 GiB across the parent and candidate scopes; assess any other active build reservations at launch time','source_revision_recorded':'d3d12f9f5540a37f456672f59c07d90d30187da2','patched_InterpExpansion_sha256':sha(src/'interp/InterpExpansion.ml'),'parent_binary_sha256':sha(parent/'aeneas-r312-slice-length-candidate')}
(audit/'build-host-reservation-before.json').write_text(json.dumps(pre,indent=2))
subprocess.run(['sudo','-n','systemctl','set-property','--runtime','aspisr344.slice','MemoryHigh=5G','MemoryMax=7G','MemorySwapMax=0','TasksMax=128'],check=True)
pre['r344_slice_before']=subprocess.check_output(['systemctl','show','aspisr344.slice','-p','MemoryHigh','-p','MemoryMax','-p','MemorySwapMax','-p','TasksMax','-p','MemoryCurrent','-p','MemoryPeak'],text=True)
(audit/'build-host-reservation-before.json').write_text(json.dumps(pre,indent=2))
inner="set -eu; cd /work/src; export OPAMJOBS=1 DUNEJOBS=1; /usr/bin/time -v env AENEAS_VERSION=aspis-r344-direct-empty-enum-candidate-20261002-a OCAMLPARAM=_,ccopt=-static opam exec -- dune build main.exe --profile release -j 1; cp _build/default/main.exe /work/aeneas-r344-direct-empty-enum-candidate; chmod 755 /work/aeneas-r344-direct-empty-enum-candidate"
docker_cmd=['docker','run','--name','aspis-r344-direct-empty-enum-candidate-build','--network','none','--memory-reservation=5g','--memory=7g','--memory-swap=7g','--pids-limit=128','--cgroup-parent=aspisr344.slice','-v',str(root)+':/work','ef96e46342a4','bash','-lc',inner]
command={'docker_argv':docker_cmd,'inner_build_command':inner,'docker_image_id':'sha256:ef96e46342a4159b6a62663e1ff5474a5f5deaf260daf08ea7b0963974418db7','profile':'dune build main.exe --profile release -j 1','optimization':'Dune release profile; static native link via OCAMLPARAM=_,ccopt=-static','parallelism':{'OPAMJOBS':1,'DUNEJOBS':1,'dune_jobs':1},'expected_work':'cached compilation of the changed InterpExpansion.ml module plus native relink; no cold dependency build or proof generation','source_revision_recorded':'d3d12f9f5540a37f456672f59c07d90d30187da2','parent_binary_sha256':'fff3717072567f291fc1444f52a3dc7c1f8ba4ddc5c3980e94c863cdceb60f4f','parent_InterpExpansion_sha256':'30dc6e75bdafa31d04b29784e8235306f569161dcd5c73f8381ae18cd17ff7cd','patched_InterpExpansion_sha256':'da68f59bc0240bad9862f0733aecd7265c239dbe988669d5d8ddddafc5a79b19','unchanged_PrePasses_sha256':'09014aa93bffd2cafeebaf23d27a301d66986d9349f4cc9dca6e8d1dfe0ba7dd','parent_source_tree_sha256':'489a55478797418ff13d89b0ed694195dadcf087f8a92626fc3a39411141f6ce','candidate_source_tree_sha256_before_build':'d1791e6864a9ca48b3f3cfcf9950b0a3872e682947f5a0b62edbb732c01c8a40','parent_binary_sha256':'fff3717072567f291fc1444f52a3dc7c1f8ba4ddc5c3980e94c863cdceb60f4f','parent_InterpExpansion_sha256':'30dc6e75bdafa31d04b29784e8235306f569161dcd5c73f8381ae18cd17ff7cd','candidate_InterpExpansion_sha256':'da68f59bc0240bad9862f0733aecd7265c239dbe988669d5d8ddddafc5a79b19','unchanged_PrePasses_sha256':'09014aa93bffd2cafeebaf23d27a301d66986d9349f4cc9dca6e8d1dfe0ba7dd'}
(audit/'build-command.json').write_text(json.dumps(command,indent=2)+'\n')
# Capture container process stats and its cgroup v2 peak files while live.
log=(audit/'build.log').open('w'); timefile=audit/'docker-cli-time.txt'; p=subprocess.Popen(['/usr/bin/time','-v','-o',str(timefile),*docker_cmd],stdout=log,stderr=subprocess.STDOUT,text=True)
container='aspis-r344-direct-empty-enum-candidate-build'; samples=[]; cgroup_paths=set()
while p.poll() is None:
 try:
  info=json.loads(subprocess.check_output(['docker','inspect',container],stderr=subprocess.DEVNULL,text=True))[0]
  pid=info.get('State',{}).get('Pid',0)
  if pid:
   cgline=next((l for l in pathlib.Path(f'/proc/{pid}/cgroup').read_text().splitlines() if l.startswith('0::')),'')
   if cgline:
    rel=cgline.split('::',1)[1].lstrip('/'); cg=pathlib.Path('/sys/fs/cgroup')/rel
    cgroup_paths.add(str(cg))
    sample={'pid':pid,'cgroup':str(cg)}
    for fname in ('memory.current','memory.peak','memory.swap.current','memory.swap.peak','memory.events'):
     try: sample[fname]= (cg/fname).read_text().strip()
     except OSError: pass
    samples.append(sample)
 except Exception as e:
  samples.append({'sample_error':type(e).__name__})
 time.sleep(.2)
log.close(); status=p.returncode
try: inspect=json.loads(subprocess.check_output(['docker','inspect',container],text=True))
except subprocess.CalledProcessError: inspect=[]
(audit/'docker-inspect.json').write_text(json.dumps(inspect,indent=2)+'\n')
(audit/'cgroup-samples.json').write_text(json.dumps({'samples':samples,'observed_container_cgroup_paths':sorted(cgroup_paths)},indent=2)+'\n')
try: slice_after=subprocess.check_output(['systemctl','show','aspisr344.slice','-p','MemoryHigh','-p','MemoryMax','-p','MemorySwapMax','-p','TasksMax','-p','MemoryCurrent','-p','MemoryPeak','-p','MemorySwapCurrent','-p','MemorySwapPeak'],text=True)
except subprocess.CalledProcessError as e: slice_after='ERROR '+str(e)
after={'meminfo_after':mem(),'r344_slice_after':slice_after,'r312_parent_slice_after':subprocess.check_output(['systemctl','show','aspisr312.slice','-p','MemoryHigh','-p','MemoryMax','-p','MemorySwapMax','-p','MemoryCurrent','-p','MemoryPeak','-p','MemorySwapCurrent','-p','MemorySwapPeak'],text=True),'active_docker_containers_after':subprocess.check_output(['docker','ps','--no-trunc','--format','{{.ID}} {{.Names}} {{.Status}}'],text=True)}
(audit/'build-host-reservation-after.json').write_text(json.dumps(after,indent=2))
binary=root/'aeneas-r344-direct-empty-enum-candidate'
result={'build_exit_status':status,'source_revision_recorded':'d3d12f9f5540a37f456672f59c07d90d30187da2','docker_image_id':'sha256:ef96e46342a4159b6a62663e1ff5474a5f5deaf260daf08ea7b0963974418db7','parent_binary_sha256':'fff3717072567f291fc1444f52a3dc7c1f8ba4ddc5c3980e94c863cdceb60f4f','patched_InterpExpansion_sha256':sha(src/'interp/InterpExpansion.ml'),'parent_source_unchanged':(sha(parent/'src/interp/InterpExpansion.ml')=='30dc6e75bdafa31d04b29784e8235306f569161dcd5c73f8381ae18cd17ff7cd' and sha(parent/'src/PrePasses.ml')=='09014aa93bffd2cafeebaf23d27a301d66986d9349f4cc9dca6e8d1dfe0ba7dd'),'cli_time_report':timefile.read_text() if timefile.exists() else None,'container_cgroup_samples':len(samples),'observed_container_cgroup_paths':sorted(cgroup_paths),'binary_exists':binary.is_file(),'binary_sha256':sha(binary) if binary.is_file() else None,'binary_size_bytes':binary.stat().st_size if binary.is_file() else None,'translation_or_Lean_compile_run':False}
(audit/'build-result.json').write_text(json.dumps(result,indent=2)+'\n')
if status: print((audit/'build.log').read_text()[-10000:])
else: print((audit/'build.log').read_text()[-10000:])
print('R344_BUILD_EXIT',status)
raise SystemExit(status)
