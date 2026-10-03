#!/usr/bin/env python3
import hashlib, json, pathlib, re, subprocess, time

root = pathlib.Path('/home/dombarker/project-offloads/aspis-r490-slice-len-builtin-20261003-a')
src = root / 'src'
audit = root / 'candidate-audit/r493-slice-len-builtin-build'
audit.mkdir(parents=True, exist_ok=True)
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
source = src / 'PrePasses.ml'
extract_source = src / 'extract/ExtractBuiltinLean.ml'
binary = src / '_build/default/main.exe'
out_binary = root / 'aeneas-r493-slice-len-builtin-candidate'
expected_source = '587ab22f412f7344aa616cbda35d47bcdaf51492e7e79caaf0ab3bc4279a7eee'
expected_extract_source = '7963be0b32879555b88960d61d5593780261f82950d06054437cbdb144a5bd16'
expected_base_source = '579f332212ad75b386b088ef7835783f7cb84a835b1acb96031d49847fc53a17'
expected_base_extract = '49eeda5d7dbf34819b9f4663fe8f2bdd276cafc0b6bf18ec00829772d700be0d'
expected_base_binary = '66b70542419d9df6040e0b57aaca3b74896de410d158bccba8274e21fdfc54c1'
image = 'ef96e46342a4'
container_name = 'aspis-r493-slice-len-builtin-build'

assert sha(source) == expected_source, sha(source)
assert sha(extract_source) == expected_extract_source, sha(extract_source)
assert sha(root / 'PrePasses.baseline.ml') == expected_base_source
assert sha(root / 'ExtractBuiltinLean.baseline.ml') == expected_base_extract
assert sha(binary) == expected_base_binary, sha(binary)
assert not out_binary.exists()
image_info = subprocess.check_output(['docker','image','inspect',image,'--format','{{.Id}} {{.Size}}'],text=True).strip()
assert image_info.startswith('sha256:ef96e46342a4159b6a62663e1ff5474a5f5deaf260daf08ea7b0963974418db7 '), image_info
assert not subprocess.check_output(['docker','ps','-a','--filter',f'name={container_name}','--format','{{.Names}}'],text=True).strip()

# Fail closed if current Aspis systemd/Docker reservations plus this build exceed 40 GiB.
def parse_systemd(command):
    text = subprocess.check_output(command, text=True)
    rows=[]
    for line in text.splitlines():
        parts=line.split()
        if not parts or not parts[0].lower().startswith('aspis'):
            continue
        name=parts[0]
        show_cmd=[command[0]] + (['--user'] if len(command)>1 and command[1]=='--user' else []) + ['show',name,'-p','MemoryMax']
        raw=subprocess.check_output(show_cmd,text=True).strip().split('=',1)[-1]
        if raw in ('infinity','0',''):
            raise RuntimeError(f'uncapped Aspis systemd unit: {name}={raw}')
        rows.append({'name':name,'memory_max_bytes':int(raw)})
    return rows
user_rows=parse_systemd(['systemctl','--user','list-units','--type=service','--state=running','--plain','--no-legend'])
system_rows=parse_systemd(['systemctl','list-units','--type=service','--state=running','--plain','--no-legend'])
docker_rows=[]
for line in subprocess.check_output(['docker','ps','--no-trunc','--format','{{.ID}} {{.Names}}'],text=True).splitlines():
    parts=line.split(maxsplit=1)
    if len(parts)==2 and parts[1].startswith('aspis'):
        inspect=json.loads(subprocess.check_output(['docker','inspect',parts[0]],text=True))[0]
        memory=inspect['HostConfig']['Memory']
        if not memory:
            raise RuntimeError(f'uncapped Aspis Docker container: {parts[1]}')
        docker_rows.append({'name':parts[1],'memory_max_bytes':memory})
reservation_bytes=sum(x['memory_max_bytes'] for x in user_rows+system_rows+docker_rows)+7*1024**3+7*1024**3
assert reservation_bytes <= 40*1024**3, {'total':reservation_bytes,'user':user_rows,'system':system_rows,'docker':docker_rows}
meminfo=pathlib.Path('/proc/meminfo').read_text()
mem_available_kib=int(re.search(r'^MemAvailable:\s+(\d+)',meminfo,re.M).group(1))
assert mem_available_kib >= 12*1024*1024, mem_available_kib

pre = {
  'workspace':str(root), 'base_source_revision':'56a931fc3879354a2fa584e73bd0a1d412714851',
  'base_release_launch_revision':'078a3bd7d4471a5f10549843e7818b956163bb77',
  'base_PrePasses_sha256':expected_base_source, 'candidate_PrePasses_sha256':sha(source),
  'base_ExtractBuiltinLean_sha256':expected_base_extract,'candidate_ExtractBuiltinLean_sha256':sha(extract_source),
  'baseline_cached_binary_sha256':sha(binary), 'docker_image_id':image_info.split()[0],
  'command':'cd /work/src && OPAMJOBS=1 DUNEJOBS=1 AENEAS_VERSION=aspis-r493-slice-len-builtin-20261003-a OCAMLPARAM=_,ccopt=-static opam exec -- dune build main.exe --profile release -j 1',
  'optimization':'Dune release profile; single job; static native link',
  'systemd_caps':{'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':'0','TasksMax':128},
  'docker_caps':{'memory_reservation':'5g','memory':'7g','memory_swap':'7g (no swap)','pids_limit':128,'network':'none'},
  'active_user_aspis_reservations':user_rows,'active_system_aspis_reservations':system_rows,'active_docker_aspis_reservations':docker_rows,
  'aggregate_maximum_with_build_scopes_bytes':reservation_bytes,'aggregate_limit_bytes':40*1024**3,
  'MemAvailable_before_kib':mem_available_kib,
}
(audit/'build-preflight.json').write_text(json.dumps(pre,indent=2)+'\n')

inner = "set -eu; cd /work/src; export OPAMJOBS=1 DUNEJOBS=1; /usr/bin/time -v -o /work/candidate-audit/r493-slice-len-builtin-build/compiler-time.txt env AENEAS_VERSION=aspis-r493-slice-len-builtin-20261003-a OCAMLPARAM=_,ccopt=-static opam exec -- dune build main.exe --profile release -j 1; cp _build/default/main.exe /work/aeneas-r493-slice-len-builtin-candidate; chmod 755 /work/aeneas-r493-slice-len-builtin-candidate"
cmd=['docker','run','--name',container_name,'--network','none','--memory-reservation=5g','--memory=7g','--memory-swap=7g','--pids-limit=128','-v',str(root)+':/work',image,'bash','-lc',inner]
(audit/'build-command.json').write_text(json.dumps({'argv':cmd,'inner_command':inner,'profile':'dune build main.exe --profile release -j 1','reason':'compile only the reviewed PrePasses change against the copied pinned cache; no translation/Lean compile'},indent=2)+'\n')
log=(audit/'build.log').open('w')
proc=subprocess.Popen(cmd,stdout=log,stderr=subprocess.STDOUT,text=True)
samples=[]; cgpaths=set()
while proc.poll() is None:
    try:
        ins=json.loads(subprocess.check_output(['docker','inspect',container_name],stderr=subprocess.DEVNULL,text=True))[0]
        pid=ins.get('State',{}).get('Pid',0)
        if pid:
            rows=pathlib.Path(f'/proc/{pid}/cgroup').read_text().splitlines()
            rel=next((r.split('::',1)[1].strip('/') for r in rows if r.startswith('0::')),None)
            if rel:
                cg=pathlib.Path('/sys/fs/cgroup')/rel; cgpaths.add(str(cg)); sample={'pid':pid,'cgroup':str(cg)}
                for f in ('memory.current','memory.peak','memory.swap.current','memory.swap.peak','memory.events'):
                    try: sample[f]=(cg/f).read_text().strip()
                    except OSError: pass
                samples.append(sample)
    except Exception as e:
        samples.append({'sample_error':type(e).__name__})
    time.sleep(.2)
log.close(); status=proc.returncode
try: docker_inspect=json.loads(subprocess.check_output(['docker','inspect',container_name],text=True))[0]
except subprocess.CalledProcessError: docker_inspect=[]
(audit/'docker-inspect.json').write_text(json.dumps(docker_inspect,indent=2)+'\n')
(audit/'cgroup-samples.json').write_text(json.dumps({'samples':samples,'observed_container_cgroup_paths':sorted(cgpaths)},indent=2)+'\n')
try: after_available=int(re.search(r'^MemAvailable:\s+(\d+)',pathlib.Path('/proc/meminfo').read_text(),re.M).group(1))
except Exception: after_available=None

def max_sample(key):
    vals=[]
    for s in samples:
        try: vals.append(int(s[key]))
        except (KeyError,ValueError): pass
    return max(vals) if vals else None

time_report=(audit/'compiler-time.txt').read_text() if (audit/'compiler-time.txt').exists() else ''
def metric(pat):
    m=re.search(pat,time_report)
    return m.group(1) if m else None
result={
 'build_exit_status':status,'source_revision':'56a931fc3879354a2fa584e73bd0a1d412714851',
 'launch_revision':'078a3bd7d4471a5f10549843e7818b956163bb77',
 'base_PrePasses_sha256':expected_base_source,'candidate_PrePasses_sha256':sha(source),
 'base_ExtractBuiltinLean_sha256':expected_base_extract,'candidate_ExtractBuiltinLean_sha256':sha(extract_source),
 'baseline_cached_binary_sha256':expected_base_binary,
 'candidate_binary_exists':out_binary.is_file(),'candidate_binary_sha256':sha(out_binary) if out_binary.is_file() else None,
 'candidate_binary_size_bytes':out_binary.stat().st_size if out_binary.is_file() else None,
 'compiler_elapsed_wall_time':metric(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (\S+)'),
 'compiler_maximum_rss_kib':metric(r'Maximum resident set size \(kbytes\): (\d+)'),
 'compiler_swap_events':metric(r'Swaps: (\d+)'),
 'container_cgroup_paths':sorted(cgpaths),'container_memory_peak_bytes':max_sample('memory.peak'),
 'container_swap_peak_bytes':max_sample('memory.swap.peak'),'container_samples':len(samples),
 'MemAvailable_after_kib':after_available,'translation_or_Lean_compile_run':False,
}
(audit/'build-result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
raise SystemExit(status)
