#!/usr/bin/env python3
"""Clone, one-line patch, and build isolated cached native Aeneas R289 candidate."""
import hashlib, json, pathlib, shlex, subprocess, sys

HERE = pathlib.Path(__file__).resolve().parent
HOST = "dombarker@100.108.41.90"
SSH_OPTS = ["-o", "BatchMode=yes", "-o", "StrictHostKeyChecking=no", "-o", "UserKnownHostsFile=/dev/null"]
SOURCE = "/home/dombarker/project-offloads/aspis-return-continuation-20261002-a/src"
REMOTE_ROOT = "/home/dombarker/project-offloads/aspis-r289-retention-candidate-20261002-a"
BASE_PREPASSES_SHA256 = "9271943fac2d2a75add181a268197a9e7eaaf2690a3b97507454d008f996d9e1"
DOCKER_IMAGE = "sha256:ef96e46342a4159b6a62663e1ff5474a5f5deaf260daf08ea7b0963974418db7"
SOURCE_REVISION = "380c7d46c9719dcfcab601fac2607861d47dee02"

REMOTE_SCRIPT = r'''import pathlib,shutil,subprocess,hashlib,difflib,json,os,stat
base=pathlib.Path("@SOURCE@")
root=pathlib.Path("@REMOTE_ROOT@")
pre=base/"PrePasses.ml"
assert base.is_dir() and (base/"_build/default/main.exe").is_file()
assert hashlib.sha256(pre.read_bytes()).hexdigest()=="@BASE_HASH@"
assert not root.exists(),f"R289 destination already exists: {root}"

def tree_state(root):
    entries=[];file_count=0;byte_count=0;symlink_count=0;regular={};symlink_source_aliases=[]
    for current,dirs,files in os.walk(root,topdown=True,followlinks=False):
        current=pathlib.Path(current)
        for name in list(dirs):
            p=current/name; rel=p.relative_to(root).as_posix()
            if p.is_symlink():
                target=os.readlink(p);entries.append([rel,"symlink-dir",target]);symlink_count+=1;dirs.remove(name)
                resolved=(p.parent/target).resolve(strict=False) if not os.path.isabs(target) else pathlib.Path(target).resolve(strict=False)
                try: resolved.relative_to(root.resolve())
                except ValueError: pass
                else:
                    if os.path.isabs(target):symlink_source_aliases.append(rel)
            else: entries.append([rel,"dir"])
        for name in files:
            p=current/name;rel=p.relative_to(root).as_posix()
            if p.is_symlink():
                target=os.readlink(p);entries.append([rel,"symlink-file",target]);symlink_count+=1
                resolved=(p.parent/target).resolve(strict=False) if not os.path.isabs(target) else pathlib.Path(target).resolve(strict=False)
                try: resolved.relative_to(root.resolve())
                except ValueError: pass
                else:
                    if os.path.isabs(target):symlink_source_aliases.append(rel)
            else:
                st=p.stat();h=hashlib.sha256()
                with p.open("rb") as f:
                    for chunk in iter(lambda:f.read(1024*1024),b""):h.update(chunk)
                digest=h.hexdigest();entries.append([rel,"file",st.st_size,digest]);regular[rel]=(st.st_dev,st.st_ino,digest,st.st_size)
                file_count+=1;byte_count+=st.st_size
    entries.sort(key=lambda x:x[0]);canonical=json.dumps(entries,separators=(",",":"),ensure_ascii=False).encode()
    return {"tree_sha256":hashlib.sha256(canonical).hexdigest(),"regular_file_count":file_count,"regular_file_bytes":byte_count,"symlink_count":symlink_count,"symlink_absolute_targets_into_source":symlink_source_aliases,"regular_files":regular,"entries":entries}

def meminfo():
    return {k:v for k,v in (line.split(":",1) for line in pathlib.Path("/proc/meminfo").read_text().splitlines()) if k in ("MemTotal","MemAvailable","SwapTotal","SwapFree")}

before=meminfo(); available=int(before["MemAvailable"].split()[0]);assert available>=24*1024*1024,before
disk=shutil.disk_usage("/home/dombarker/project-offloads")._asdict()
image=subprocess.check_output(["docker","image","inspect","@DOCKER_SHORT@","--format","{{.Id}} {{.Size}}"],text=True).strip()
assert image.startswith("@DOCKER_IMAGE@ "),image
active_docker=subprocess.check_output(["docker","ps","--format","{{.ID}} {{.Names}} {{.Status}}"],text=True)
active_scopes=subprocess.check_output(["systemctl","--user","list-units","--type=service","--state=running","--no-legend"],text=True)
assert not [line for line in active_docker.splitlines() if "aspis-" in line],active_docker
assert not [line for line in active_scopes.splitlines() if "aspis-r" in line and "aspis-r289-retention-candidate-build.service" not in line],active_scopes
slice_before=subprocess.check_output(["systemctl","show","aspisr289.slice","-p","MemoryHigh","-p","MemoryMax","-p","MemorySwapMax","-p","TasksMax","-p","MemoryCurrent","-p","MemoryPeak"],text=True)
source_state=tree_state(base)
assert not source_state["symlink_absolute_targets_into_source"],source_state["symlink_absolute_targets_into_source"]
assert disk["free"] > source_state["regular_file_bytes"] + 10*1024**3,(disk,source_state["regular_file_bytes"])
preflight={"meminfo_before":before,"disk_usage_before":disk,"source_tree_before":{k:v for k,v in source_state.items() if k!="entries" and k!="regular_files"},"base_PrePasses_sha256":hashlib.sha256(pre.read_bytes()).hexdigest(),"source_git_dir_present":(base/".git").exists(),"docker_image_inspect":image,"active_docker_containers_before":active_docker,"active_user_services_before":active_scopes,"aspisr289_slice_existing_before":slice_before,"source_campaign_revision_recorded":"@SOURCE_REVISION@","source_path":str(base),"remote_destination":str(root)}
root.mkdir()
(root/"host-reservation-before.json").write_text(json.dumps(preflight,indent=2))
shutil.copytree(base,root/"src",symlinks=True,copy_function=shutil.copy2)
clone=root/"src"
clone_state_before=tree_state(clone)
assert clone_state_before["tree_sha256"]==source_state["tree_sha256"],(clone_state_before["tree_sha256"],source_state["tree_sha256"])
shared=[]
for rel,(dev,ino,digest,size) in source_state["regular_files"].items():
    cloned=clone/rel;st=cloned.stat();assert (st.st_size,hashlib.sha256(cloned.read_bytes()).hexdigest())==(size,digest),rel
    if (st.st_dev,st.st_ino)==(dev,ino):shared.append(rel)
assert not shared,shared[:10]
clone_before=tree_state(clone);p=clone/"PrePasses.ml";old=p.read_text()
needle="      if f.item_meta.is_local then visitor#visit_fun_decl_id () f.def_id;"
replacement="      if f.item_meta.is_local || (match f.body with StructuredBody _ -> true | _ -> false) then visitor#visit_fun_decl_id () f.def_id;"
assert old.count(needle)==1,old.count(needle)
new=old.replace(needle,replacement)
assert new.count(replacement)==1 and new.count(needle)==0
p.write_text(new)
diff="".join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile="a/src/PrePasses.ml",tofile="b/src/PrePasses.ml"))
added=[x for x in diff.splitlines() if x.startswith("+") and not x.startswith("+++")]
removed=[x for x in diff.splitlines() if x.startswith("-") and not x.startswith("---")]
assert added==["+"+replacement] and removed==["-"+needle],diff
clone_after=tree_state(clone)
assert set(clone_before["regular_files"])==set(clone_after["regular_files"])
changed=[rel for rel,(dev,ino,digest,size) in clone_before["regular_files"].items() if clone_after["regular_files"].get(rel,(None,None,None,None))[2]!=digest]
assert changed==["PrePasses.ml"],changed
(root/"source-delta.patch").write_text(diff)
prepatch={k:v for k,v in clone_before.items() if k not in ("entries","regular_files")}
postpatch={k:v for k,v in clone_after.items() if k not in ("entries","regular_files")}
(root/"whole-tree-hashes.json").write_text(json.dumps({"source_before_copy":preflight["source_tree_before"],"clone_before_patch":prepatch,"clone_after_patch":postpatch,"only_changed_relative_path":["PrePasses.ml"],"shared_regular_file_inodes":shared},indent=2))
(root/"source-adapter.json").write_text(json.dumps({"source_campaign_revision_recorded":"@SOURCE_REVISION@","frozen_source_root":str(base),"frozen_source_root_git_metadata_present":preflight["source_git_dir_present"],"parent_PrePasses_sha256":hashlib.sha256(old.encode()).hexdigest(),"patched_PrePasses_sha256":hashlib.sha256(new.encode()).hexdigest(),"patch_change_count":{"added":1,"removed":1},"exact_old_line":needle,"exact_new_line":replacement,"unified_diff":diff,"copy_mode":"shutil.copytree(symlinks=True,copy_function=shutil.copy2); identical source/clone tree hashes before patch; no regular-file inode sharing"},indent=2))

subprocess.run(["sudo","-n","systemctl","set-property","--runtime","aspisr289.slice","MemoryHigh=5G","MemoryMax=7G","MemorySwapMax=0","TasksMax=128"],check=True)
slice_ready=subprocess.check_output(["systemctl","show","aspisr289.slice","-p","MemoryHigh","-p","MemoryMax","-p","MemorySwapMax","-p","TasksMax","-p","MemoryCurrent","-p","MemoryPeak"],text=True)
(root/"slice-properties-before-build.txt").write_text(slice_ready)
build="set -eu; cd /work/src; export OPAMJOBS=1 DUNEJOBS=1; AENEAS_VERSION=aspis-r289-retention-candidate-20261002-a OCAMLPARAM=_,ccopt=-static opam exec -- dune build main.exe --profile release -j 1; cp _build/default/main.exe /work/aeneas-r289-retention-candidate; chmod 755 /work/aeneas-r289-retention-candidate"
cmd=["docker","run","--name","aspis-r289-retention-candidate-build","--network","none","--memory-reservation=5g","--memory=7g","--memory-swap=7g","--pids-limit=128","--cgroup-parent=aspisr289.slice","-v",str(root)+":/work","@DOCKER_SHORT@","bash","-lc",build]
(root/"build-command.json").write_text(json.dumps({"command":cmd,"shell_build":build,"docker_image_id":"@DOCKER_IMAGE@","profile":"dune build main.exe --profile release -j 1","static":"OCAMLPARAM=_,ccopt=-static","time_expectation":"cached incremental compilation of the modified OCaml module and native relink only; no proof generation","systemd_limits":{"MemoryHigh":"5G","MemoryMax":"7G","MemorySwapMax":"0","TasksMax":128},"docker_limits":{"memory_reservation":"5g","memory":"7g","memory_swap":"7g (equal to memory; no container swap)","pids_limit":128,"network":"none","cgroup_parent":"aspisr289.slice"},"source_campaign_revision_recorded":"@SOURCE_REVISION@"},indent=2))
with (root/"build.log").open("w") as f:r=subprocess.run(["/usr/bin/time","-v",*cmd],stdout=f,stderr=subprocess.STDOUT)
(root/"docker-inspect.json").write_bytes(subprocess.check_output(["docker","inspect","aspis-r289-retention-candidate-build"]))
(root/"slice-properties-after-build.txt").write_bytes(subprocess.check_output(["systemctl","show","aspisr289.slice","-p","MemoryHigh","-p","MemoryMax","-p","MemorySwapMax","-p","TasksMax","-p","MemoryCurrent","-p","MemoryPeak","-p","MemorySwapCurrent","-p","MemorySwapPeak"]))
clone_after_build=tree_state(clone)
base_after=tree_state(base)
post={"meminfo_after_build":meminfo(),"disk_usage_after":shutil.disk_usage("/home/dombarker/project-offloads")._asdict(),"source_tree_after":{k:v for k,v in base_after.items() if k not in ("entries","regular_files")},"source_unchanged":base_after["tree_sha256"]==source_state["tree_sha256"],"clone_after_build":{k:v for k,v in clone_after_build.items() if k not in ("entries","regular_files")},"active_docker_containers_after":subprocess.check_output(["docker","ps","--format","{{.ID}} {{.Names}} {{.Status}}"],text=True),"aspisr289_slice_after":subprocess.check_output(["systemctl","show","aspisr289.slice","-p","MemoryHigh","-p","MemoryMax","-p","MemorySwapMax","-p","TasksMax","-p","MemoryCurrent","-p","MemoryPeak","-p","MemorySwapCurrent","-p","MemorySwapPeak"],text=True)}
(root/"host-reservation-after.json").write_text(json.dumps(post,indent=2))
status={"build_exit_status":r.returncode,"source_campaign_revision_recorded":"@SOURCE_REVISION@","parent_PrePasses_sha256":hashlib.sha256(old.encode()).hexdigest(),"patched_PrePasses_sha256":hashlib.sha256(new.encode()).hexdigest(),"source_unchanged":post["source_unchanged"],"changed_clone_paths_since_prepatch":["PrePasses.ml"]}
binary=root/"aeneas-r289-retention-candidate"
if r.returncode==0:
    status["binary_sha256"]=hashlib.sha256(binary.read_bytes()).hexdigest()
    status["binary_size_bytes"]=binary.stat().st_size
    (root/"binary-version.txt").write_text(subprocess.check_output([str(binary),"-version"],text=True))
    (root/"binary-file.txt").write_text(subprocess.check_output(["file",str(binary)],text=True))
(root/"build-result.json").write_text(json.dumps(status,indent=2))
print((root/"build.log").read_text()[-5000:]);print("R289_BUILD_EXIT",r.returncode)
raise SystemExit(r.returncode)
'''

mapping={"@SOURCE@":SOURCE,"@REMOTE_ROOT@":REMOTE_ROOT,"@BASE_HASH@":BASE_PREPASSES_SHA256,
         "@DOCKER_IMAGE@":DOCKER_IMAGE,"@DOCKER_SHORT@":"ef96e46342a4","@SOURCE_REVISION@":SOURCE_REVISION,
    }
remote_script=REMOTE_SCRIPT
for key,value in mapping.items(): remote_script=remote_script.replace(key,value)
argv=["systemd-run","--user","--wait","--collect","--pipe","--unit=aspis-r289-retention-candidate-build",
      "--working-directory=/home/dombarker/project-offloads/aspis-return-continuation-20261002-a",
      "-p","MemoryHigh=5G","-p","MemoryMax=7G","-p","MemorySwapMax=0","-p","TasksMax=128","python3","-c",remote_script]
ssh_argv=["ssh",*SSH_OPTS,HOST,shlex.join(argv)]
(HERE/"build-launch.json").write_text(json.dumps({"systemd_argv":argv,"ssh_argv":ssh_argv,
    "caps":{"MemoryHigh":"5G","MemoryMax":"7G","MemorySwapMax":"0","TasksMax":128},
    "docker_image_id":DOCKER_IMAGE,"source_revision_recorded":SOURCE_REVISION},indent=2)+"\n")
with (HERE/"build-launch.log").open("w") as out: result=subprocess.run(ssh_argv,stdout=out,stderr=subprocess.STDOUT)
print((HERE/"build-launch.log").read_text()[-3000:])
artifacts=["source-delta.patch","source-adapter.json","whole-tree-hashes.json","host-reservation-before.json","host-reservation-after.json",
          "slice-properties-before-build.txt","slice-properties-after-build.txt","build-command.json","build.log","docker-inspect.json",
          "build-result.json","binary-version.txt","binary-file.txt","aeneas-r289-retention-candidate","src/PrePasses.ml"]
for rel in artifacts:
    copied=subprocess.run(["scp",*SSH_OPTS,f"{HOST}:{REMOTE_ROOT}/{rel}",str(HERE/rel)])
    if copied.returncode and rel not in ("aeneas-r289-retention-candidate","binary-version.txt","binary-file.txt"):
        sys.exit(copied.returncode)
if result.returncode: sys.exit(result.returncode)
status=json.loads((HERE/"build-result.json").read_text())
assert status["build_exit_status"]==0 and status["source_unchanged"] is True
assert status["parent_PrePasses_sha256"]==BASE_PREPASSES_SHA256
assert hashlib.sha256((HERE/"src/PrePasses.ml").read_bytes()).hexdigest()==status["patched_PrePasses_sha256"]
assert hashlib.sha256((HERE/"aeneas-r289-retention-candidate").read_bytes()).hexdigest()==status["binary_sha256"]
sys.exit(0)
