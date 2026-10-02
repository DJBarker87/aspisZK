#!/usr/bin/env python3
"""Clone, one-line patch, statically build, and translate the retained R210 input."""
import hashlib
import json
import pathlib
import shlex
import subprocess
import sys

HERE = pathlib.Path(__file__).resolve().parent
HOST = "dombarker@100.108.41.90"
SSH_OPTS = ["-o", "BatchMode=yes", "-o", "StrictHostKeyChecking=no", "-o", "UserKnownHostsFile=/dev/null"]
REMOTE_ROOT = "/home/dombarker/project-offloads/aspis-r214-copy-routing-20261002-a"
REMOTE_SRC = "/home/dombarker/project-offloads/aspis-return-continuation-20261002-a/src"
SOURCE_REVISION = "237d48bc3f70c262a27e9a8595b9ac51d12b4e77"
ORIGINAL_PREPASSES_SHA256 = "9271943fac2d2a75add181a268197a9e7eaaf2690a3b97507454d008f996d9e1"
R210_LLB = "/home/dombarker/project-offloads/aspis-r210-vector-leaf-diagnostic-20261002-a/R210VectorLeaf.llbc"
R210_LLB_SHA256 = "b8ecd783e8c71da66dd929d43d7f5054521752fc7e111b2db102f16c5166fae5"
DOCKER_IMAGE_ID = "sha256:ef96e46342a4159b6a62663e1ff5474a5f5deaf260daf08ea7b0963974418db7"

BUILD_SCRIPT = r'''import pathlib,shutil,subprocess,hashlib,difflib,json,os,re
base=pathlib.Path("@REMOTE_SRC@")
root=pathlib.Path("@REMOTE_ROOT@")
assert base.is_dir() and (base/"_build").is_dir()
assert not root.exists(),f"R214 target already exists: {root}"
pre=base/"PrePasses.ml"
original=pre.read_text()
original_hash=hashlib.sha256(pre.read_bytes()).hexdigest()
assert original_hash=="@ORIGINAL_PREPASSES_SHA256@",original_hash
root.mkdir()
shutil.copytree(base,root/"src",symlinks=True,copy_function=shutil.copy2)
copied=root/"src"
assert (copied/"_build/default/main.exe").is_file()
# Verify an ordinary copy: each copied regular file has a distinct inode.
file_count=0;byte_count=0;shared_inodes=[]
for src_path in base.rglob("*"):
    rel=src_path.relative_to(base);dst_path=copied/rel
    if src_path.is_symlink():
        assert dst_path.is_symlink() and os.readlink(src_path)==os.readlink(dst_path)
    elif src_path.is_file():
        a=src_path.stat();b=dst_path.stat();file_count+=1;byte_count+=a.st_size
        if (a.st_dev,a.st_ino)==(b.st_dev,b.st_ino):shared_inodes.append(str(rel))
assert not shared_inodes,shared_inodes[:5]
p=copied/"PrePasses.ml";old=p.read_text()
needle="        | SetDiscriminant _ | Assert (_, _, _) | Call (_, _) | Error _ ->"
replacement="        | SetDiscriminant _ | Assert (_, _, _) | Call (_, _) | Error _ | CopyNonOverlapping _ ->"
assert old.count(needle)==1,old.count(needle)
new=old.replace(needle,replacement)
p.write_text(new)
diff="".join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile="a/src/PrePasses.ml",tofile="b/src/PrePasses.ml"))
added=[x for x in diff.splitlines() if x.startswith("+") and not x.startswith("+++")]
removed=[x for x in diff.splitlines() if x.startswith("-") and not x.startswith("---")]
assert len(added)==1 and len(removed)==1 and added[0][1:]==replacement and removed[0][1:]==needle,diff
(root/"source-delta.patch").write_text(diff)
(root/"source-adapter.json").write_text(json.dumps({"source_revision_recorded":"@SOURCE_REVISION@","source_revision_basis":"lead-specified source revision; source snapshot has no captured git revision here","source_path":str(base),"clone_path":str(copied),"cached_build_dir_copied":True,"copy_mode":"shutil.copytree with shutil.copy2; symlinks preserved; no regular-file inode sharing verified","copied_regular_file_count":file_count,"copied_regular_file_bytes":byte_count,"shared_regular_file_inodes":shared_inodes,"original_PrePasses_sha256":original_hash,"patched_PrePasses_sha256":hashlib.sha256(p.read_bytes()).hexdigest(),"unified_diff":diff,"changed_source_lines_added":len(added),"changed_source_lines_removed":len(removed),"patch_effect":"CopyNonOverlapping remains intact and is classified with existing non-inlinable effect statements; no interpreter or pointer semantics changed"},indent=2))
preflight={"meminfo_before":{k:v for k,v in (line.split(":",1) for line in pathlib.Path("/proc/meminfo").read_text().splitlines()) if k in ("MemTotal","MemAvailable","SwapTotal","SwapFree")},"disk_usage_project_offloads":shutil.disk_usage("/home/dombarker/project-offloads")._asdict(),"source_prepass_sha256":original_hash,"docker_image_inspect":subprocess.check_output(["docker","image","inspect","ef96e46342a4","--format","{{.Id}} {{.Size}}"],text=True).strip(),"existing_switchglobal_slice":subprocess.check_output(["systemctl","show","aspisswitchglobal.slice","-p","MemoryHigh","-p","MemoryMax","-p","MemorySwapMax","-p","MemoryCurrent","-p","MemoryPeak"],text=True),"active_docker_containers":subprocess.check_output(["docker","ps","--format","{{.ID}} {{.Names}} {{.Status}}"],text=True)}
assert preflight["docker_image_inspect"].startswith("@DOCKER_IMAGE_ID@ ")
available=int(preflight["meminfo_before"]["MemAvailable"].split()[0])
assert available>=24*1024*1024,available
subprocess.run(["sudo","-n","systemctl","set-property","--runtime","aspisr214.slice","MemoryHigh=5G","MemoryMax=7G","MemorySwapMax=0","TasksMax=128"],check=True)
slice_before=subprocess.check_output(["systemctl","show","aspisr214.slice","-p","MemoryHigh","-p","MemoryMax","-p","MemorySwapMax","-p","TasksMax","-p","MemoryCurrent","-p","MemoryPeak"],text=True)
(root/"host-reservation-before.json").write_text(json.dumps(preflight,indent=2))
(root/"slice-properties-before.txt").write_text(slice_before)
image="ef96e46342a4"
build="set -eu; cd /work/src; export OPAMJOBS=1 DUNEJOBS=1; AENEAS_VERSION=aspis-r214-copy-routing-20261002-a OCAMLPARAM=_,ccopt=-static opam exec -- dune build main.exe --profile release -j 1; cp _build/default/main.exe /work/aeneas-copy-routing; chmod 755 /work/aeneas-copy-routing"
cmd=["docker","run","--name","aspis-r214-copy-routing-build","--network","none","--memory-reservation=5g","--memory=7g","--memory-swap=7g","--pids-limit=128","--cgroup-parent=aspisr214.slice","-v",str(root)+":/work",image,"bash","-lc",build]
(root/"build-command.json").write_text(json.dumps({"command":cmd,"shell_build":build,"docker_image_id":preflight["docker_image_inspect"].split()[0],"release":"dune build main.exe --profile release -j 1","static":"OCAMLPARAM=_,ccopt=-static","limits":{"docker_memory_reservation":"5g","docker_memory":"7g","docker_memory_swap":"7g (equal to memory; no container swap)","docker_pids_limit":128,"cgroup_parent":"aspisr214.slice"},"source_revision_recorded":"@SOURCE_REVISION@"},indent=2))
with (root/"build.log").open("w") as f:r=subprocess.run(["/usr/bin/time","-v",*cmd],stdout=f,stderr=subprocess.STDOUT)
(root/"docker-inspect.json").write_bytes(subprocess.check_output(["docker","inspect","aspis-r214-copy-routing-build"]))
(root/"slice-properties-after-build.txt").write_bytes(subprocess.check_output(["systemctl","show","aspisr214.slice","-p","MemoryHigh","-p","MemoryMax","-p","MemorySwapMax","-p","TasksMax","-p","MemoryCurrent","-p","MemoryPeak","-p","MemorySwapCurrent","-p","MemorySwapPeak"]))
post={"meminfo_after_build":{k:v for k,v in (line.split(":",1) for line in pathlib.Path("/proc/meminfo").read_text().splitlines()) if k in ("MemTotal","MemAvailable","SwapTotal","SwapFree")},"active_docker_containers_after_build":subprocess.check_output(["docker","ps","--format","{{.ID}} {{.Names}} {{.Status}}"],text=True)}
(root/"host-reservation-after.json").write_text(json.dumps(post,indent=2))
status={"build_exit_status":r.returncode,"source_revision_recorded":"@SOURCE_REVISION@","patched_PrePasses_sha256":hashlib.sha256(p.read_bytes()).hexdigest()}
binary=root/"aeneas-copy-routing"
if r.returncode==0:
    status["binary_sha256"]=hashlib.sha256(binary.read_bytes()).hexdigest()
    (root/"binary-version.txt").write_text(subprocess.check_output([str(binary),"-version"],text=True))
(root/"build-result.json").write_text(json.dumps(status,indent=2))
print((root/"build.log").read_text()[-4000:]);print("R214_BUILD_EXIT",r.returncode)
raise SystemExit(r.returncode)
'''

TRANSLATE_SCRIPT = r'''import pathlib,subprocess,json,hashlib
root=pathlib.Path("@REMOTE_ROOT@")
src=pathlib.Path("@R210_LLB@")
binary=root/"aeneas-copy-routing"
assert src.is_file() and hashlib.sha256(src.read_bytes()).hexdigest()=="@R210_LLB_SHA256@"
assert binary.is_file()
cmd=[str(binary),"-sequential","-no-progress-bar","-abort-on-error","-backend","lean","-namespace","AspisR210VectorLeaf","-dest",str(root/"generated"),"-subdir","AspisR210VectorLeaf","-split-files","-emit-json",str(src)]
(root/"translate-command.json").write_text(json.dumps({"command":cmd,"input_sha256":hashlib.sha256(src.read_bytes()).hexdigest(),"binary_sha256":hashlib.sha256(binary.read_bytes()).hexdigest(),"input_unchanged_from_R210":True,"flags_unchanged_from_R210":True},indent=2))
with (root/"translate.log").open("w") as f:r=subprocess.run(["/usr/bin/time","-v",*cmd],stdout=f,stderr=subprocess.STDOUT)
(root/"translate-result.json").write_text(json.dumps({"translate_exit_status":r.returncode,"input_sha256":hashlib.sha256(src.read_bytes()).hexdigest(),"binary_sha256":hashlib.sha256(binary.read_bytes()).hexdigest(),"generated_dir_exists":(root/"generated").exists()},indent=2))
(root/"slice-properties-after-translate.txt").write_bytes(subprocess.check_output(["systemctl","show","aspisr214.slice","-p","MemoryHigh","-p","MemoryMax","-p","MemorySwapMax","-p","TasksMax","-p","MemoryCurrent","-p","MemoryPeak","-p","MemorySwapCurrent","-p","MemorySwapPeak"]))
print((root/"translate.log").read_text()[-5000:]);print("R214_TRANSLATE_EXIT",r.returncode)
raise SystemExit(r.returncode)
'''

def substitute(source: str, mapping: dict[str, str]) -> str:
    for key, value in mapping.items():
        source = source.replace(key, value)
    return source

def launch(unit: str, script: str, logfile: pathlib.Path) -> int:
    argv = ["systemd-run", "--user", "--wait", "--collect", "--pipe", f"--unit={unit}",
            "--working-directory=/home/dombarker/project-offloads/aspis-return-continuation-20261002-a",
            "-p", "MemoryHigh=5G", "-p", "MemoryMax=7G", "-p", "MemorySwapMax=0", "-p", "TasksMax=128",
            "python3", "-c", script]
    ssh_argv = ["ssh", *SSH_OPTS, HOST, shlex.join(argv)]
    descriptor = {"systemd_argv": argv, "ssh_argv": ssh_argv,
                 "caps": {"MemoryHigh":"5G","MemoryMax":"7G","MemorySwapMax":"0","TasksMax":128}}
    (HERE / f"{unit}-launch.json").write_text(json.dumps(descriptor, indent=2) + "\n")
    with logfile.open("w") as output:
        result = subprocess.run(ssh_argv, stdout=output, stderr=subprocess.STDOUT)
    print(logfile.read_text()[-2000:])
    return result.returncode

def scp_file(remote_path: str, local_path: pathlib.Path) -> int:
    local_path.parent.mkdir(parents=True, exist_ok=True)
    argv = ["scp", *SSH_OPTS, f"{HOST}:{remote_path}", str(local_path)]
    return subprocess.run(argv).returncode

mapping = {"@REMOTE_SRC@":REMOTE_SRC,"@REMOTE_ROOT@":REMOTE_ROOT,
           "@ORIGINAL_PREPASSES_SHA256@":ORIGINAL_PREPASSES_SHA256,
           "@SOURCE_REVISION@":SOURCE_REVISION,"@DOCKER_IMAGE_ID@":DOCKER_IMAGE_ID,
           "@R210_LLB@":R210_LLB,"@R210_LLB_SHA256@":R210_LLB_SHA256}
build_script = substitute(BUILD_SCRIPT,mapping)
translate_script = substitute(TRANSLATE_SCRIPT,mapping)

build_exit = launch("aspis-r214-copy-routing-build", build_script, HERE / "build-launch.log")
build_artifacts = ["source-delta.patch","source-adapter.json","host-reservation-before.json","host-reservation-after.json",
                   "slice-properties-before.txt","slice-properties-after-build.txt","build-command.json","build.log",
                   "docker-inspect.json","build-result.json","binary-version.txt","aeneas-copy-routing","src/PrePasses.ml"]
for relative in build_artifacts:
    if scp_file(f"{REMOTE_ROOT}/{relative}",HERE/relative):
        if relative not in {"binary-version.txt","aeneas-copy-routing"} or build_exit==0:
            print("missing build artifact",relative)
if build_exit:
    sys.exit(build_exit)

translate_exit = launch("aspis-r214-copy-routing-translate", translate_script, HERE / "translate-launch.log")
for relative in ["translate-command.json","translate.log","translate-result.json","slice-properties-after-translate.txt"]:
    scp_file(f"{REMOTE_ROOT}/{relative}",HERE/relative)
# Preserve generated Lean output if the translator produced it; translation is
# diagnostic only and no Lean compilation follows.
check = ["ssh",*SSH_OPTS,HOST,f"test -d {shlex.quote(REMOTE_ROOT + '/generated')}"]
if subprocess.run(check).returncode==0:
    subprocess.run(["scp","-r",*SSH_OPTS,f"{HOST}:{REMOTE_ROOT}/generated",str(HERE)])
sys.exit(translate_exit)
