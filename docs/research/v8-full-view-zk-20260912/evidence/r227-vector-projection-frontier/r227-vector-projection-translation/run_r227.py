#!/usr/bin/env python3
"""Run exactly one capped diagnostic translation of the corrected R220 projection."""
import hashlib
import json
import pathlib
import shlex
import subprocess

HERE = pathlib.Path(__file__).resolve().parent
HOST = "dombarker@100.108.41.90"
REMOTE_ROOT = "/home/dombarker/project-offloads/aspis-r227-vector-projection-translation-20261002-a"
INPUT = f"{REMOTE_ROOT}/R220ReachableProjection.llbc"
BINARY = f"{REMOTE_ROOT}/aeneas-copy-operands"
INPUT_SHA = "5bff089f4502d4a3a6bf90cb679807e25265d309ca9c509976996a62be26551b"
BINARY_SHA = "7e3be7b0c24975c248ad769c80bac2cc896a5f1b89c2858b8f01a6024cf80ae3"
UNIT = "aspis-r227-vector-projection-translate"
SSH_OPTS = ["-o", "BatchMode=yes", "-o", "StrictHostKeyChecking=no", "-o", "UserKnownHostsFile=/dev/null"]

REMOTE_PY = r'''import datetime,hashlib,json,pathlib,subprocess,sys
root=pathlib.Path("@ROOT@")
src=root/"R220ReachableProjection.llbc"
binpath=root/"aeneas-copy-operands"
expected_src="@INPUT_SHA@"
expected_bin="@BINARY_SHA@"
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert src.is_file() and sha(src)==expected_src,sha(src) if src.exists() else "missing input"
assert binpath.is_file() and sha(binpath)==expected_bin,sha(binpath) if binpath.exists() else "missing binary"
cmd=[str(binpath),"-sequential","-no-progress-bar","-abort-on-error","-backend","lean","-namespace","AspisR220VectorProjection","-dest",str(root/"generated"),"-subdir","AspisR220VectorProjection","-split-files","-emit-json",str(src)]
(root/"translate-command.json").write_text(json.dumps({"command":cmd,"input_sha256":sha(src),"binary_sha256":sha(binpath),"input_bytes":src.stat().st_size,"binary_bytes":binpath.stat().st_size,"source_revision":"ab9260ef1","source_revision_basis":"lead-specified repository source revision; translator binary copied unchanged from audited R215 build"},indent=2)+"\n")
mem={}
for line in pathlib.Path("/proc/meminfo").read_text().splitlines():
 k,v=line.split(":",1);mem[k]=v.strip()
(root/"host-reservation-at-start.json").write_text(json.dumps({"captured_utc":datetime.datetime.now(datetime.timezone.utc).isoformat(),"MemTotal":mem.get("MemTotal"),"MemAvailable":mem.get("MemAvailable"),"SwapTotal":mem.get("SwapTotal"),"SwapFree":mem.get("SwapFree")},indent=2)+"\n")
with (root/"translate.log").open("w") as f:r=subprocess.run(["/usr/bin/time","-v",*cmd],stdout=f,stderr=subprocess.STDOUT)
unit=subprocess.run(["systemctl","--user","show","@UNIT@.service","-p","ActiveState","-p","MemoryHigh","-p","MemoryMax","-p","MemorySwapMax","-p","TasksMax","-p","MemoryCurrent","-p","MemoryPeak","-p","MemorySwapCurrent","-p","MemorySwapPeak"],text=True,capture_output=True)
mem2={}
for line in pathlib.Path("/proc/meminfo").read_text().splitlines():
 k,v=line.split(":",1);mem2[k]=v.strip()
(root/"host-reservation-at-end.json").write_text(json.dumps({"captured_utc":datetime.datetime.now(datetime.timezone.utc).isoformat(),"MemTotal":mem2.get("MemTotal"),"MemAvailable":mem2.get("MemAvailable"),"SwapTotal":mem2.get("SwapTotal"),"SwapFree":mem2.get("SwapFree"),"systemd_unit_properties":unit.stdout,"systemd_show_returncode":unit.returncode},indent=2)+"\n")
(root/"translate-result.json").write_text(json.dumps({"child_exit_status":r.returncode,"input_sha256":sha(src),"binary_sha256":sha(binpath),"generated_dir_exists":(root/"generated").exists(),"source_revision":"ab9260ef1","raw_log":"translate.log"},indent=2)+"\n")
print("R227_TRANSLATE_CHILD_EXIT",r.returncode)
print((root/"translate.log").read_text()[-6500:])
sys.exit(r.returncode)
'''
remote_py = REMOTE_PY.replace("@ROOT@", REMOTE_ROOT).replace("@INPUT_SHA@", INPUT_SHA).replace("@BINARY_SHA@", BINARY_SHA).replace("@UNIT@", UNIT)
argv = ["systemd-run", "--user", "--wait", "--collect", "--pipe", f"--unit={UNIT}", f"--working-directory={REMOTE_ROOT}", "-p", "MemoryHigh=5G", "-p", "MemoryMax=7G", "-p", "MemorySwapMax=0", "-p", "TasksMax=128", "python3", "-c", remote_py]
ssh_argv = ["ssh", *SSH_OPTS, HOST, shlex.join(argv)]
(HERE / "translate-launch.json").write_text(json.dumps({"systemd_argv": argv, "ssh_argv": ssh_argv, "caps": {"MemoryHigh":"5G", "MemoryMax":"7G", "MemorySwapMax":"0", "TasksMax":128}, "fresh_remote_root":REMOTE_ROOT, "input_sha256":INPUT_SHA, "binary_sha256":BINARY_SHA, "source_revision":"ab9260ef1"},indent=2)+"\n")
with (HERE / "translate-launch.log").open("w") as f:
    result = subprocess.run(ssh_argv, stdout=f, stderr=subprocess.STDOUT)
(HERE / "launcher-result.json").write_text(json.dumps({"ssh_systemd_run_returncode":result.returncode,"unit":UNIT},indent=2)+"\n")
for name in ["translate-command.json","translate.log","translate-result.json","host-reservation-at-start.json","host-reservation-at-end.json"]:
    subprocess.run(["scp",*SSH_OPTS,f"{HOST}:{REMOTE_ROOT}/{name}",str(HERE/name)],check=False)
subprocess.run(["ssh",*SSH_OPTS,HOST,f"test -d {shlex.quote(REMOTE_ROOT+'/generated')}"],stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL)
if subprocess.run(["ssh",*SSH_OPTS,HOST,f"test -d {shlex.quote(REMOTE_ROOT+'/generated')}"],stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL).returncode==0:
    subprocess.run(["scp","-r",*SSH_OPTS,f"{HOST}:{REMOTE_ROOT}/generated",str(HERE)],check=False)
print((HERE/"translate-launch.log").read_text()[-8000:])
print("SYSTEMD_RUN_RETURN",result.returncode)
