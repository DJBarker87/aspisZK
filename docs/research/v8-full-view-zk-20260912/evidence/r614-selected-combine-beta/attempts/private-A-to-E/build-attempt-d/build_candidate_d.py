#!/usr/bin/env python3
"""Fail-closed R614 Docker/OPAM optimized-build launcher. Preparation only by default.

The R614 worker must supply source-manifest.json with the four changed source
hashes. Root must review the generated launch plan before invoking --execute.
"""
import argparse
import base64
import hashlib
import json
import pathlib
import re
import shlex
import subprocess
import sys

HERE = pathlib.Path(__file__).resolve().parent
HOST = "dombarker@100.108.41.90"
SSH_OPTS = ["-o", "BatchMode=yes", "-o", "ConnectTimeout=5", "-o", "StrictHostKeyChecking=no", "-o", "UserKnownHostsFile=/dev/null"]
PARENT = "/home/dombarker/project-offloads/aspis-v7-aeneas-source-unblock-20260830/aeneas-diagnostic-source"
CANDIDATE = "/home/dombarker/project-offloads/aspis-r614-scalar-constants-candidate-20261004-a"
OUTPUT = "/home/dombarker/project-offloads/aspis-r614-scalar-constants-build-output-20261004-d"
IMAGE = "sha256:ef96e46342a4159b6a62663e1ff5474a5f5deaf260daf08ea7b0963974418db7"
SLICE = "aspisr614.slice"
UNIT = "aspis-r614-scalar-constants-build-20261004-d"
CONTAINER = "aspis-r614-scalar-constants-container-20261004-d"
BINARY = "aeneas-r614-scalar-constants-candidate-20261004-d"
PARENT_COMMIT = "1d31b733124394b34195a6abdb3bca7a312d46f1"
PARENT_SHA = {
    "src/extract/Extract.ml": "caf4139ec75cdfb721ed44e823e49134927035b1d0655a050d07c06e3fc0cd14",
    "src/interp/InterpStatements.ml": "061c0b53ee02aa2b19ab2998ad84a7a5e3f3add06f66deaec839f8dff7343982",
    "src/interp/InterpExpressions.ml": "531b0ee1c6d26d463d07c6e1dbdc75a7cce32cf970adcbc59dfafd75bfdd914f",
    "src/interp/InterpExpressions.mli": "f0a15cdb3a491148f9bad38077c9c5126411fb5ea4502e38ba1bcb44153371e1",
}
MANIFEST = HERE / "source-manifest.json"
REMOTE = r'''import hashlib,json,pathlib,re,subprocess,sys,time
cfg=json.loads(sys.argv[1]); parent=pathlib.Path(cfg["parent"]); root=pathlib.Path(cfg["candidate"]); output=pathlib.Path(cfg["output"])
files=cfg["files"]; image=cfg["image"]; expected_image=cfg["image_id"]; slice_name=cfg["slice"]
unit=cfg["unit"]; container=cfg["container"]; binary_name=cfg["binary"]
GiB=1024**3

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def check(ok,msg):
    if not ok: raise SystemExit(msg)
def status(path): return subprocess.check_output(["git","-C",str(path),"status","--porcelain"],text=True)
def status_paths(s): return {line[3:] for line in s.splitlines() if len(line)>=4}

check(parent.is_dir() and root.is_dir(),"parent or candidate tree is missing")
check(subprocess.check_output(["git","-C",str(parent),"rev-parse","HEAD"],text=True).strip()==cfg["parent_commit"],"pinned original parent revision mismatch")
parent_head=subprocess.check_output(["git","-C",str(parent),"rev-parse","HEAD"],text=True).strip()
candidate_head=subprocess.check_output(["git","-C",str(root),"rev-parse","HEAD"],text=True).strip()
check(candidate_head==parent_head,"candidate HEAD does not match original parent HEAD")
parent_status_before=status(parent); candidate_status_before=status(root)
# The diagnostic parent deliberately has pre-existing changes. Require the candidate
# to carry that baseline plus exactly the two authorized new source-path changes.
check(parent_status_before==cfg["parent_status_before_prepare"],"original parent status differs from exact preparation baseline")
check(candidate_status_before==cfg["candidate_status_after_prepare"],"candidate status differs from exact preparation baseline")
for rel,pins in files.items():
    check(sha(parent/rel)==pins["parent_sha256"],f"original pinned source hash mismatch: {rel}")
    check(sha(root/rel)==pins["candidate_sha256"],f"candidate source hash mismatch: {rel}")
output.mkdir(parents=True,exist_ok=True)
outbin=output/binary_name
check(not outbin.exists(),f"refusing to overwrite candidate binary: {outbin}")
image_id=subprocess.check_output(["docker","image","inspect",image,"--format","{{.Id}}"],text=True).strip()
check(image_id==expected_image,f"pinned image id mismatch: {image_id}")

# Record live memory and all active Aspis user-unit reservations before launch.
mi={}
for line in pathlib.Path("/proc/meminfo").read_text().splitlines():
    if ":" in line:
        k,v=line.split(":",1); mi[k]=v.strip()
memavail_kib=int(mi["MemAvailable"].split()[0])
check(memavail_kib*1024>=15*GiB,f"MemAvailable below 15GiB build+OS/control reserve: {mi['MemAvailable']}")
active=subprocess.check_output(["systemctl","--user","list-units","--type=service","--state=running","--plain","--no-legend"],text=True)
reservations=[]
for line in active.splitlines():
    cols=line.split()
    if cols and cols[0].startswith("aspis"):
        raw=subprocess.check_output(["systemctl","--user","show",cols[0],"-p","MemoryMax"],text=True).strip().split("=",1)[1]
        if raw.isdigit(): reservations.append((cols[0],int(raw)))
reserved=sum(v for _,v in reservations)
# Account separately for the capped user unit and its capped Docker container.
added=14*GiB
check(reserved+added<=40*GiB,f"aggregate Aspis reservations + systemd 7GiB + Docker 7GiB exceeds 40GiB: {reservations}")
set_slice=subprocess.run(["sudo","-n","systemctl","set-property","--runtime",slice_name,"MemoryHigh=5G","MemoryMax=7G","MemorySwapMax=0","TasksMax=128"],capture_output=True,text=True)
check(set_slice.returncode==0,f"failed to set dedicated system slice: {set_slice.stderr}")
slice_before=subprocess.check_output(["systemctl","show",slice_name,"-p","MemoryHigh","-p","MemoryMax","-p","MemorySwapMax","-p","TasksMax","-p","MemoryCurrent","-p","MemoryPeak"],text=True)

inner=("set -eu; cd /work/src; export OPAMJOBS=1 DUNEJOBS=1; "
 " /usr/bin/time -v -o /output/R614-compiler-time.txt env "
 "AENEAS_VERSION=aspis-r614-scalar-constants-candidate-20261004-d "
 "OCAMLPARAM=_,ccopt=-static opam exec -- dune build main.exe --profile release -j 1; "
 "install -m 755 _build/default/main.exe /output/"+binary_name)
docker_argv=["docker","run","--rm","--name",container,"--network","none",
 "--memory-reservation=5g","--memory=7g","--memory-swap=7g","--pids-limit=128",
 "--cgroup-parent="+slice_name,"-v",str(root)+":/work","-v",str(output)+":/output",
 image,"bash","-lc",inner]
unit_argv=["systemd-run","--user","--wait","--collect","--pipe","--unit="+unit,
 "--working-directory="+str(root/"src"),"-p","MemoryHigh=5G","-p","MemoryMax=7G",
 "-p","MemorySwapMax=0","-p","TasksMax=128","-p","RuntimeMaxSec=600s","--",
 "/usr/bin/time","-v","-o",str(output/"R614-unit-time.txt"),*docker_argv]
pre={"target":"private Aeneas optimized release build only","parent":str(parent),"parent_commit":parent_head,
 "candidate":str(root),"candidate_commit":candidate_head,
 "parent_status_before":parent_status_before,"candidate_status_before":candidate_status_before,
 "source_hashes_before":{"parent":{p:sha(parent/p) for p in files},"candidate":{p:sha(root/p) for p in files}},
 "pinned_docker_image":image_id,"meminfo":{"MemAvailable":mi["MemAvailable"],"MemTotal":mi.get("MemTotal"),"SwapFree":mi.get("SwapFree"),"SwapTotal":mi.get("SwapTotal")},
 "existing_aspis_user_reservations":reservations,"existing_reservations_bytes":reserved,
 "added_systemd_limit_bytes":7*GiB,"added_docker_limit_bytes":7*GiB,"aggregate_limit_bytes":40*GiB,
 "system_slice_before":slice_before,"docker_argv":docker_argv,"remote_systemd_argv":unit_argv,"inner_release_command":inner,
 "resource_caps":{"systemd_user_unit":{"MemoryHigh":"5G","MemoryMax":"7G","MemorySwapMax":0,"TasksMax":128,"RuntimeMaxSec":"600s"},
 "effective_docker":{"memory_reservation":"5g","memory":"7g","memory_swap":"7g (equal to memory; swap disabled)","pids_limit":128,"cgroup_parent":slice_name}},
 "expected_changed_sources":files}
(output/"R614-build-command.json").write_text(json.dumps(pre,indent=2)+"\n")
log=output/"R614-docker-build.log"; wall_start=time.monotonic()
with log.open("w") as stream:
    try:
        proc=subprocess.run(unit_argv,stdout=stream,stderr=subprocess.STDOUT,timeout=630)
        status_code=proc.returncode
    except subprocess.TimeoutExpired:
        status_code=124
elapsed=time.monotonic()-wall_start
# Docker daemon jobs do not live inside the client unit. Stop this owned private
# job if the capped client exited while the container is still running.
probe=subprocess.run(["docker","inspect",container,"--format","{{.State.Running}}"],capture_output=True,text=True)
container_stop=None
if probe.returncode==0 and probe.stdout.strip()=="true":
    stop=subprocess.run(["docker","stop","-t","5",container],capture_output=True,text=True)
    container_stop={"exit_status":stop.returncode,"stdout":stop.stdout,"stderr":stop.stderr}
    check(stop.returncode==0,"owned private compiler container could not be stopped")
parent_status_after=status(parent); candidate_status_after=status(root)
for rel,pins in files.items():
    check(sha(parent/rel)==pins["parent_sha256"],f"original parent source mutated: {rel}")
    check(sha(root/rel)==pins["candidate_sha256"],f"candidate source changed during compilation: {rel}")
check(parent_status_after==parent_status_before,"original parent status changed during build")
check(candidate_status_after==candidate_status_before,"candidate status changed during build (expected _build ignored)")
slice_after=subprocess.check_output(["systemctl","show",slice_name,"-p","MemoryHigh","-p","MemoryMax","-p","MemorySwapMax","-p","TasksMax","-p","MemoryCurrent","-p","MemoryPeak","-p","MemorySwapCurrent","-p","MemorySwapPeak"],text=True)

def parse_gnu_time(path):
    if not path.exists(): return {}
    text=path.read_text(errors="replace")
    def field(pattern):
        match=re.search(pattern,text)
        return match.group(1) if match else None
    return {"elapsed_wall_clock":field(r"Elapsed \(wall clock\) time \(h:mm:ss or m:ss\):\s*(\S+)"),
            "peak_rss_kib":field(r"Maximum resident set size \(kbytes\):\s*(\d+)"),
            "swaps":field(r"Swaps:\s*(\d+)")}
compiler_time=parse_gnu_time(output/"R614-compiler-time.txt")
unit_time=parse_gnu_time(output/"R614-unit-time.txt")
binary=output/binary_name
result={"exit_status":status_code,"elapsed_python_seconds":elapsed,"owned_container_stop":container_stop,"binary_exists":binary.is_file(),
 "binary_sha256":sha(binary) if binary.is_file() else None,"binary_bytes":binary.stat().st_size if binary.is_file() else None,
 "compiler_gnu_time":compiler_time,"systemd_unit_gnu_time":unit_time,
 "parent_source_hashes_after":{p:sha(parent/p) for p in files},"candidate_source_hashes_after":{p:sha(root/p) for p in files},
 "parent_status_after":parent_status_after,"candidate_status_after":candidate_status_after,"system_slice_after":slice_after,
 "formal_axioms":"N/A; optimized compiler build only","build_command":"opam exec -- dune build main.exe --profile release -j 1"}
(output/"R614-build-result.json").write_text(json.dumps(result,indent=2)+"\n")
print(json.dumps(result))
sys.exit(status_code)
'''


def load_manifest():
    if not MANIFEST.is_file():
        raise SystemExit(f"R614 hashes not yet supplied: expected {MANIFEST}; refusing guessed pins")
    m = json.loads(MANIFEST.read_text())
    if m.get("parent") != PARENT or m.get("candidate") != CANDIDATE or m.get("parent_commit") != PARENT_COMMIT:
        raise SystemExit("R614 manifest parent/candidate/revision mismatch")
    entries = m.get("files")
    if not isinstance(entries, list) or {e.get("path") for e in entries} != set(PARENT_SHA):
        raise SystemExit("R614 manifest must contain exactly the four authorized source paths")
    by_path = {e["path"]:e for e in entries}
    for p, original in PARENT_SHA.items():
        if by_path[p].get("parent_sha256") != original:
            raise SystemExit(f"R614 manifest has wrong original SHA for {p}")
        new = by_path[p].get("candidate_sha256","")
        if not re.fullmatch(r"[0-9a-f]{64}",new) or new == original:
            raise SystemExit(f"R614 manifest missing valid changed SHA for {p}")
    return m, by_path


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--execute",action="store_true",help="run only after lead review; default is plan generation")
    args=parser.parse_args()
    m, entries=load_manifest()
    files={p:{"parent_sha256":PARENT_SHA[p],"candidate_sha256":entries[p]["candidate_sha256"]} for p in sorted(PARENT_SHA)}
    cfg={"parent":PARENT,"candidate":CANDIDATE,"output":OUTPUT,"parent_commit":PARENT_COMMIT,
         "image":IMAGE,"image_id":IMAGE,"slice":SLICE,"unit":UNIT,"container":CONTAINER,"binary":BINARY,"files":files,
         "parent_status_before_prepare":m["parent_status_before_prepare"],
         "candidate_status_after_prepare":m["candidate_status_after_prepare"]}
    payload64=base64.b64encode(REMOTE.encode()).decode("ascii")
    remote_py="import base64; exec(base64.b64decode("+repr(payload64)+"))"
    remote_command="python3 -c "+shlex.quote(remote_py)+" "+shlex.quote(json.dumps(cfg))
    ssh_argv=["ssh",*SSH_OPTS,HOST,remote_command]
    launch={"prepared_only":not args.execute,"parent":PARENT,"candidate":CANDIDATE,"manifest_sha256":hashlib.sha256(MANIFEST.read_bytes()).hexdigest(),
      "candidate_source_hashes":{p:e["candidate_sha256"] for p,e in entries.items()},"ssh_argv":ssh_argv,
      "systemd_unit":UNIT,"docker_container":CONTAINER,"binary":OUTPUT+"/"+BINARY,
      "image":IMAGE,"systemd_caps":{"MemoryHigh":"5G","MemoryMax":"7G","MemorySwapMax":0,"TasksMax":128,"RuntimeMaxSec":"600s"},
      "docker_caps":{"memory-reservation":"5g","memory":"7g","memory-swap":"7g","pids-limit":128,"cgroup-parent":SLICE},
      "no_verifier_or_source_change":True,"formal_axioms":"N/A; build only"}
    plan=HERE/"launch-plan.json"; plan.write_text(json.dumps(launch,indent=2)+"\n")
    if not args.execute:
        print(f"Prepared launch plan only: {plan}; no SSH/build/translation was run.")
        return
    local_log=HERE/"R614-ssh-launch.log"
    with local_log.open("w") as f:
        proc=subprocess.run(ssh_argv,stdout=f,stderr=subprocess.STDOUT)
    # Fetch exact remote inputs/results even when the build fails. Missing paths are
    # recorded in the SSH log; no remote cleanup or source mutation is performed.
    scp_base=["scp",*SSH_OPTS]
    for name in ["R614-build-command.json","R614-docker-build.log","R614-compiler-time.txt","R614-unit-time.txt","R614-build-result.json",BINARY]:
        subprocess.run([*scp_base,f"{HOST}:{OUTPUT}/{name}",str(HERE/name)],check=False,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL)
    print(f"R614 remote launcher exit={proc.returncode}; local log={local_log}")
    sys.exit(proc.returncode)

if __name__=="__main__": main()
