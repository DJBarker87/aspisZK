#!/usr/bin/env python3
"""Clone R214's cached source, add one operand visitor case, build and translate once."""
import hashlib
import json
import pathlib
import shlex
import subprocess
import sys

HERE = pathlib.Path(__file__).resolve().parent
HOST = "dombarker@100.108.41.90"
SSH_OPTS = ["-o", "BatchMode=yes", "-o", "StrictHostKeyChecking=no", "-o", "UserKnownHostsFile=/dev/null"]
REMOTE_ROOT = "/home/dombarker/project-offloads/aspis-r215-copy-operands-20261002-a"
REMOTE_SRC = "/home/dombarker/project-offloads/aspis-r214-copy-routing-20261002-a/src"
SOURCE_CAMPAIGN = "9f15ca80a"
PARENT_PREPASSES_SHA256 = "92a8e2e8de4d8357acef2fe5c76f900aeb1d49588cfe15db9ba38d2ad2265e99"
R210_LLB = "/home/dombarker/project-offloads/aspis-r210-vector-leaf-diagnostic-20261002-a/R210VectorLeaf.llbc"
R210_LLB_SHA256 = "b8ecd783e8c71da66dd929d43d7f5054521752fc7e111b2db102f16c5166fae5"
DOCKER_IMAGE_ID = "sha256:ef96e46342a4159b6a62663e1ff5474a5f5deaf260daf08ea7b0963974418db7"

BUILD_SCRIPT = r'''import pathlib,shutil,subprocess,hashlib,difflib,json,os
base=pathlib.Path("@REMOTE_SRC@")
root=pathlib.Path("@REMOTE_ROOT@")
assert base.is_dir() and (base/"_build").is_dir()
assert not root.exists(),f"R215 target already exists: {root}"
pre=base/"PrePasses.ml"
original_hash=hashlib.sha256(pre.read_bytes()).hexdigest()
assert original_hash=="@PARENT_PREPASSES_SHA256@",original_hash
root.mkdir()
shutil.copytree(base,root/"src",symlinks=True,copy_function=shutil.copy2)
copied=root/"src"
assert (copied/"_build/default/main.exe").is_file()
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
needle="            | Switch (If (cond, yes, no)) ->"
branch=("            | CopyNonOverlapping { src; dst; count } ->\n"
        "                CopyNonOverlapping\n"
        "                  { src = visitor#visit_operand mk_unit_ty src;\n"
        "                    dst = visitor#visit_operand mk_unit_ty dst;\n"
        "                    count = visitor#visit_operand mk_unit_ty count }")
assert old.count(needle)==1,old.count(needle)
assert old.count("            | CopyNonOverlapping { src; dst; count } ->")==0
new=old.replace(needle,branch+"\n"+needle)
p.write_text(new)
diff="".join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile="a/src/PrePasses.ml",tofile="b/src/PrePasses.ml"))
added=[x for x in diff.splitlines() if x.startswith("+") and not x.startswith("+++")]
removed=[x for x in diff.splitlines() if x.startswith("-") and not x.startswith("---")]
expected=set(branch.split("\n"))
assert not removed and len(added)==5 and {x[1:] for x in added}==expected,diff
(root/"source-delta.patch").write_text(diff)
(root/"source-adapter.json").write_text(json.dumps({"source_campaign_recorded":"@SOURCE_CAMPAIGN@","source_revision_basis":"campaign identifier lead-specified; copied Aeneas source snapshot has no captured Git revision","source_path":str(base),"clone_path":str(copied),"parent_source_PrePasses_sha256":original_hash,"patched_PrePasses_sha256":hashlib.sha256(p.read_bytes()).hexdigest(),"copy_mode":"shutil.copytree with shutil.copy2; symlinks preserved; no regular-file inode sharing verified","copied_regular_file_count":file_count,"copied_regular_file_bytes":byte_count,"shared_regular_file_inodes":shared_inodes,"expected_added_branch_lines":5,"removed_source_lines":0,"unified_diff":diff,"patch_effect":"CopyNonOverlapping src/dst/count operands pass through the existing visitor; statement remains intact; no interpreter or pointer semantics changed"},indent=2))
preflight={"meminfo_before":{k:v for k,v in (line.split(":",1) for line in pathlib.Path("/proc/meminfo").read_text().splitlines()) if k in ("MemTotal","MemAvailable","SwapTotal","SwapFree")},"disk_usage_project_offloads":shutil.disk_usage("/home/dombarker/project-offloads")._asdict(),"parent_prepass_sha256":original_hash,"docker_image_inspect":subprocess.check_output(["docker","image","inspect","ef96e46342a4","--format","{{.Id}} {{.Size}}"],text=True).strip(),"existing_switchglobal_slice":subprocess.check_output(["systemctl","show","aspisswitchglobal.slice","-p","MemoryHigh","-p","MemoryMax","-p","MemorySwapMax","-p","MemoryCurrent","-p","MemoryPeak"],text=True),"existing_r214_slice":subprocess.check_output(["systemctl","show","aspisr214.slice","-p","MemoryHigh","-p","MemoryMax","-p","MemorySwapMax","-p","MemoryCurrent","-p","MemoryPeak"],text=True),"active_docker_containers":subprocess.check_output(["docker","ps","--format","{{.ID}} {{.Names}} {{.Status}}"],text=True)}
assert preflight["docker_image_inspect"].startswith("@DOCKER_IMAGE_ID@ ")
available=int(preflight["meminfo_before"]["MemAvailable"].split()[0])
assert available>=24*1024*1024,available
subprocess.run(["sudo","-n","systemctl","set-property","--runtime","aspisr215.slice","MemoryHigh=5G","MemoryMax=7G","MemorySwapMax=0","TasksMax=128"],check=True)
slice_before=subprocess.check_output(["systemctl","show","aspisr215.slice","-p","MemoryHigh","-p","MemoryMax","-p","MemorySwapMax","-p","TasksMax","-p","MemoryCurrent","-p","MemoryPeak"],text=True)
(root/"host-reservation-before.json").write_text(json.dumps(preflight,indent=2))
(root/"slice-properties-before.txt").write_text(slice_before)
build="set -eu; cd /work/src; export OPAMJOBS=1 DUNEJOBS=1; AENEAS_VERSION=aspis-r215-copy-operands-20261002-a OCAMLPARAM=_,ccopt=-static opam exec -- dune build main.exe --profile release -j 1; cp _build/default/main.exe /work/aeneas-copy-operands; chmod 755 /work/aeneas-copy-operands"
cmd=["docker","run","--name","aspis-r215-copy-operands-build","--network","none","--memory-reservation=5g","--memory=7g","--memory-swap=7g","--pids-limit=128","--cgroup-parent=aspisr215.slice","-v",str(root)+":/work", "ef96e46342a4","bash","-lc",build]
(root/"build-command.json").write_text(json.dumps({"command":cmd,"shell_build":build,"docker_image_id":preflight["docker_image_inspect"].split()[0],"release":"dune build main.exe --profile release -j 1","static":"OCAMLPARAM=_,ccopt=-static","limits":{"docker_memory_reservation":"5g","docker_memory":"7g","docker_memory_swap":"7g (equal to memory; no container swap)","docker_pids_limit":128,"cgroup_parent":"aspisr215.slice"},"source_campaign_recorded":"@SOURCE_CAMPAIGN@"},indent=2))
with (root/"build.log").open("w") as f:r=subprocess.run(["/usr/bin/time","-v",*cmd],stdout=f,stderr=subprocess.STDOUT)
(root/"docker-inspect.json").write_bytes(subprocess.check_output(["docker","inspect","aspis-r215-copy-operands-build"]))
(root/"slice-properties-after-build.txt").write_bytes(subprocess.check_output(["systemctl","show","aspisr215.slice","-p","MemoryHigh","-p","MemoryMax","-p","MemorySwapMax","-p","TasksMax","-p","MemoryCurrent","-p","MemoryPeak","-p","MemorySwapCurrent","-p","MemorySwapPeak"]))
post={"meminfo_after_build":{k:v for k,v in (line.split(":",1) for line in pathlib.Path("/proc/meminfo").read_text().splitlines()) if k in ("MemTotal","MemAvailable","SwapTotal","SwapFree")},"active_docker_containers_after_build":subprocess.check_output(["docker","ps","--format","{{.ID}} {{.Names}} {{.Status}}"],text=True)}
(root/"host-reservation-after.json").write_text(json.dumps(post,indent=2))
status={"build_exit_status":r.returncode,"source_campaign_recorded":"@SOURCE_CAMPAIGN@","patched_PrePasses_sha256":hashlib.sha256(p.read_bytes()).hexdigest()}
binary=root/"aeneas-copy-operands"
if r.returncode==0:
    status["binary_sha256"]=hashlib.sha256(binary.read_bytes()).hexdigest()
    (root/"binary-version.txt").write_text(subprocess.check_output([str(binary),"-version"],text=True))
(root/"build-result.json").write_text(json.dumps(status,indent=2))
print((root/"build.log").read_text()[-4000:]);print("R215_BUILD_EXIT",r.returncode)
raise SystemExit(r.returncode)
'''

TRANSLATE_SCRIPT = r'''import pathlib,subprocess,json,hashlib
root=pathlib.Path("@REMOTE_ROOT@")
src=pathlib.Path("@R210_LLB@")
binary=root/"aeneas-copy-operands"
assert src.is_file() and hashlib.sha256(src.read_bytes()).hexdigest()=="@R210_LLB_SHA256@"
assert binary.is_file()
cmd=[str(binary),"-sequential","-no-progress-bar","-abort-on-error","-backend","lean","-namespace","AspisR210VectorLeaf","-dest",str(root/"generated"),"-subdir","AspisR210VectorLeaf","-split-files","-emit-json",str(src)]
(root/"translate-command.json").write_text(json.dumps({"command":cmd,"input_sha256":hashlib.sha256(src.read_bytes()).hexdigest(),"binary_sha256":hashlib.sha256(binary.read_bytes()).hexdigest(),"input_unchanged_from_R210":True,"flags_unchanged_from_R210":True},indent=2))
with (root/"translate.log").open("w") as f:r=subprocess.run(["/usr/bin/time","-v",*cmd],stdout=f,stderr=subprocess.STDOUT)
(root/"translate-result.json").write_text(json.dumps({"translate_exit_status":r.returncode,"input_sha256":hashlib.sha256(src.read_bytes()).hexdigest(),"binary_sha256":hashlib.sha256(binary.read_bytes()).hexdigest(),"generated_dir_exists":(root/"generated").exists()},indent=2))
(root/"slice-properties-after-translate.txt").write_bytes(subprocess.check_output(["systemctl","show","aspisr215.slice","-p","MemoryHigh","-p","MemoryMax","-p","MemorySwapMax","-p","TasksMax","-p","MemoryCurrent","-p","MemoryPeak","-p","MemorySwapCurrent","-p","MemorySwapPeak"]))
print((root/"translate.log").read_text()[-5000:]);print("R215_TRANSLATE_EXIT",r.returncode)
raise SystemExit(r.returncode)
'''

def substitute(source: str, mapping: dict[str, str]) -> str:
    for key, value in mapping.items():
        source = source.replace(key, value)
    return source

def launch(unit: str, script: str, logfile: pathlib.Path) -> int:
    argv=["systemd-run","--user","--wait","--collect","--pipe",f"--unit={unit}","--working-directory=/home/dombarker/project-offloads/aspis-return-continuation-20261002-a","-p","MemoryHigh=5G","-p","MemoryMax=7G","-p","MemorySwapMax=0","-p","TasksMax=128","python3","-c",script]
    ssh_argv=["ssh",*SSH_OPTS,HOST,shlex.join(argv)]
    (HERE/f"{unit}-launch.json").write_text(json.dumps({"systemd_argv":argv,"ssh_argv":ssh_argv,"caps":{"MemoryHigh":"5G","MemoryMax":"7G","MemorySwapMax":"0","TasksMax":128}},indent=2)+"\n")
    with logfile.open("w") as output:r=subprocess.run(ssh_argv,stdout=output,stderr=subprocess.STDOUT)
    print(logfile.read_text()[-2000:]);return r.returncode

def scp_file(remote_path: str, local_path: pathlib.Path) -> int:
    local_path.parent.mkdir(parents=True,exist_ok=True)
    return subprocess.run(["scp",*SSH_OPTS,f"{HOST}:{remote_path}",str(local_path)]).returncode

mapping={"@REMOTE_SRC@":REMOTE_SRC,"@REMOTE_ROOT@":REMOTE_ROOT,"@PARENT_PREPASSES_SHA256@":PARENT_PREPASSES_SHA256,"@SOURCE_CAMPAIGN@":SOURCE_CAMPAIGN,"@DOCKER_IMAGE_ID@":DOCKER_IMAGE_ID,"@R210_LLB@":R210_LLB,"@R210_LLB_SHA256@":R210_LLB_SHA256}
build_script=substitute(BUILD_SCRIPT,mapping);translate_script=substitute(TRANSLATE_SCRIPT,mapping)
build_exit=launch("aspis-r215-copy-operands-build",build_script,HERE/"build-launch.log")
artifacts=["source-delta.patch","source-adapter.json","host-reservation-before.json","host-reservation-after.json","slice-properties-before.txt","slice-properties-after-build.txt","build-command.json","build.log","docker-inspect.json","build-result.json","binary-version.txt","aeneas-copy-operands","src/PrePasses.ml"]
for relative in artifacts:
    if scp_file(f"{REMOTE_ROOT}/{relative}",HERE/relative):
        print("missing build artifact",relative)
if build_exit:sys.exit(build_exit)
translate_exit=launch("aspis-r215-copy-operands-translate",translate_script,HERE/"translate-launch.log")
for relative in ["translate-command.json","translate.log","translate-result.json","slice-properties-after-translate.txt"]:
    scp_file(f"{REMOTE_ROOT}/{relative}",HERE/relative)
check=["ssh",*SSH_OPTS,HOST,f"test -d {shlex.quote(REMOTE_ROOT+'/generated')}"]
if subprocess.run(check).returncode==0:subprocess.run(["scp","-r",*SSH_OPTS,f"{HOST}:{REMOTE_ROOT}/generated",str(HERE)])
sys.exit(translate_exit)
