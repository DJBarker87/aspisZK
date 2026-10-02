#!/usr/bin/env python3
"""Translate the exact unchanged R297 monomorphized LLBC once in the pinned capped host."""
import hashlib, json, pathlib, shlex, subprocess, sys

HERE = pathlib.Path(__file__).resolve().parent
HOST = "dombarker@100.108.41.90"
SSH_OPTS = ["-o", "BatchMode=yes", "-o", "StrictHostKeyChecking=no", "-o", "UserKnownHostsFile=/dev/null"]
REMOTE_WORKTREE = "/home/dombarker/project-offloads/aspis-r20-r117-primal-20260930-a"
REMOTE_ROOT = "/home/dombarker/project-offloads/aspis-r303-private-batch-translation-20261002-a"
SOURCE = "/home/dombarker/project-offloads/aspis-r297-private-norm-batch-monomorphized-20261002-a/R297PrivateNormBatch.llbc"
BINARY = "/home/dombarker/project-offloads/aspis-return-continuation-20261002-a/aeneas-return-continuation"
SOURCE_SHA256 = "6c2caba33f39adecdfc7c4facd7444ab66d505956d51036d52765b1340f84de0"
BINARY_SHA256 = "63b04a88532b8fb0aaa0d274881b5cacf00bc4f449243ece905178f0de9cc495"
SOURCE_REVISION = "b87e6b73671c5bf747de1b0bf3dd324fc428912c"
ROOT_RUST_NAME = "aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::batch"

REMOTE_SCRIPT = r'''import pathlib,hashlib,subprocess,json,re
root=pathlib.Path("@REMOTE_ROOT@");assert not root.exists(),f'output root exists: {root}';root.mkdir()
source=pathlib.Path("@SOURCE@");binary=pathlib.Path("@BINARY@")
source_sha=hashlib.sha256(source.read_bytes()).hexdigest();binary_sha=hashlib.sha256(binary.read_bytes()).hexdigest()
assert source_sha=="@SOURCE_SHA@",source_sha
assert binary_sha=="@BINARY_SHA@",binary_sha
raw=json.loads(source.read_text()); assert raw["has_errors"] is False
tr=raw["translated"]; assert tr["options"]["start_from"]==["crate::circle_norm::joined_inverse::line_norm::r110_norm::batch"]
root_fun=next(x for x in tr["fun_decls"] if isinstance(x,dict) and x.get("def_id")==0)
assert root_fun["item_meta"]["is_local"] is True and root_fun.get("body") not in (None,"Opaque")
root_group_index=next(i for i,x in enumerate(tr["ordered_decls"]) if x=={"Fun":{"NonRec":0}})
mem={k:v for k,v in (line.split(':',1) for line in pathlib.Path('/proc/meminfo').read_text().splitlines()) if k in ('MemTotal','MemAvailable','SwapTotal','SwapFree')}
assert int(mem['MemAvailable'].split()[0])>=24*1024*1024,mem
r289=subprocess.check_output(['systemctl','show','aspisr289.slice','-p','MemoryHigh','-p','MemoryMax','-p','MemorySwapMax','-p','MemoryCurrent'],text=True)
existing=subprocess.check_output(['systemctl','--user','list-units','--type=service','--state=running','--no-legend'],text=True)
reservation={'meminfo_before':mem,'r289_slice_before':r289,'active_user_services':existing,'memory_available_kib':int(mem['MemAvailable'].split()[0]),'reserved_target_MemoryMax':'R289 reservation observed separately; R303 adds 7G; current MemAvailable checked >= 24GiB','caps':{'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':'0','TasksMax':128},'source_revision_recorded':'@SOURCE_REV@','source_revision_basis':'current preparation worktree revision; R297 LLBC is pinned by SHA and does not derive its revision from this field','source_sha256':source_sha,'binary_sha256':binary_sha}
(root/'host-reservation-before.json').write_text(json.dumps(reservation,indent=2))
subprocess.run(['sudo','-n','systemctl','set-property','--runtime','aspisr303.slice','MemoryHigh=5G','MemoryMax=7G','MemorySwapMax=0','TasksMax=128'],check=True)
reservation['r303_slice_before']=subprocess.check_output(['systemctl','show','aspisr303.slice','-p','MemoryHigh','-p','MemoryMax','-p','MemorySwapMax','-p','TasksMax','-p','MemoryCurrent','-p','MemoryPeak'],text=True)
(root/'host-reservation-before.json').write_text(json.dumps(reservation,indent=2))
cmd=[str(binary),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','AspisR303PrivateBatch','-dest',str(root/'generated'),'-subdir','AspisR303PrivateBatch','-split-files','-emit-json',str(source)]
(root/'translate-command.json').write_text(json.dumps({'command':cmd,'source_sha256':source_sha,'source_revision_recorded':'@SOURCE_REV@','binary_sha256':binary_sha,'namespace':'AspisR303PrivateBatch','sequential':True,'abort_on_error':True,'split_files':True,'emit_json':True,'source_gate':{'has_errors':raw['has_errors'],'root_id':0,'root_rust_name':'@ROOT_NAME@','root_group_index':root_group_index,'root_group':{'Fun':{'NonRec':0}},'root_local':True,'root_body_present':True}},indent=2))
with (root/'translate.log').open('w') as f:r=subprocess.run(['/usr/bin/time','-v',*cmd],stdout=f,stderr=subprocess.STDOUT)
print((root/'translate.log').read_text());print('TRANSLATE_EXIT',r.returncode)
gen=root/'generated';manifest=gen/'translation.json';functions=[];root_entries=[];lean_root_occurrences=[];root_entry=None;root_line=None
if manifest.is_file():
 md=json.loads(manifest.read_text());functions=md.get('functions',[])
 root_entries=[f for f in functions if f.get('rust_name')=='@ROOT_NAME@' and f.get('lean_name')=='AspisR303PrivateBatch.circle_norm.joined_inverse.line_norm.r110_norm.batch']
 if len(root_entries)==1:
  root_entry=root_entries[0]
  lp=gen/root_entry['lean_file']
  if lp.is_file():
   lines=lp.read_text(errors='replace').splitlines()
   needle='def circle_norm.joined_inverse.line_norm.r110_norm.batch'
   matches=[i for i,line in enumerate(lines,1) if line==needle]
   if len(matches)==1:
    root_line=matches[0];lean_root_occurrences=[str(lp.relative_to(gen))]
template_files={'functions':gen/'AspisR303PrivateBatch'/'FunsExternal_Template.lean','types':gen/'AspisR303PrivateBatch'/'TypesExternal_Template.lean'}
template_holes={k:(re.findall(r'^axiom\s+([^\s(]+)',v.read_text(errors='replace'),re.M) if v.is_file() else []) for k,v in template_files.items()}
warns=[line for line in (root/'translate.log').read_text(errors='replace').splitlines() if '[Warn' in line]
generated_hashes={str(v.relative_to(root)):hashlib.sha256(v.read_bytes()).hexdigest() for v in sorted(gen.rglob('*')) if v.is_file()} if gen.is_dir() else {}
metrics={'translator_exit_status':r.returncode,'generated_dir_exists':gen.is_dir(),'translation_json_exists':manifest.is_file(),'function_manifest_entries':len(functions),'required_batch_root_manifest_matches':len(root_entries),'required_batch_root_entry':root_entry,'required_batch_root_lean_files':lean_root_occurrences,'required_batch_root_lean_definition_line':root_line,'root_in_lean_source':root_line is not None,'external_template_axiom_holes':template_holes,'translator_warnings':warns,'generated_file_sha256':generated_hashes}
(root/'translation-result.json').write_text(json.dumps(metrics,indent=2))
after={'r303_slice_after':subprocess.check_output(['systemctl','show','aspisr303.slice','-p','MemoryHigh','-p','MemoryMax','-p','MemorySwapMax','-p','TasksMax','-p','MemoryCurrent','-p','MemoryPeak','-p','MemorySwapCurrent','-p','MemorySwapPeak'],text=True),'meminfo_after':{k:v for k,v in (line.split(':',1) for line in pathlib.Path('/proc/meminfo').read_text().splitlines()) if k in ('MemTotal','MemAvailable','SwapTotal','SwapFree')}}
(root/'host-reservation-after.json').write_text(json.dumps(after,indent=2))
(root/'result.json').write_text(json.dumps({'translator_exit_status':r.returncode,'root_emission':metrics,'source_sha256':source_sha,'binary_sha256':binary_sha,'source_revision_recorded':'@SOURCE_REV@','scope':'Translation inventory only; no template was filled or Lean compiled.'},indent=2))
raise SystemExit(r.returncode)
'''

def sub(src, mapping):
    for k,v in mapping.items(): src=src.replace(k,v)
    return src
mapping={"@REMOTE_ROOT@":REMOTE_ROOT,"@SOURCE@":SOURCE,"@BINARY@":BINARY,"@SOURCE_SHA@":SOURCE_SHA256,"@BINARY_SHA@":BINARY_SHA256,"@SOURCE_REV@":SOURCE_REVISION,"@ROOT_NAME@":ROOT_RUST_NAME}
remote_script=sub(REMOTE_SCRIPT,mapping)
outer=["systemd-run","--user","--wait","--collect","--pipe","--unit=aspis-r303-private-batch-translation","--working-directory="+REMOTE_WORKTREE,"-p","MemoryHigh=5G","-p","MemoryMax=7G","-p","MemorySwapMax=0","-p","TasksMax=128","python3","-c",remote_script]
ssh_argv=["ssh",*SSH_OPTS,HOST,shlex.join(outer)]
(HERE/"launch.json").write_text(json.dumps({"ssh_argv":ssh_argv,"systemd_argv":outer,"caps":{"MemoryHigh":"5G","MemoryMax":"7G","MemorySwapMax":"0","TasksMax":128},"remote_worktree":REMOTE_WORKTREE,"remote_output_root":REMOTE_ROOT,"source":SOURCE,"source_sha256":SOURCE_SHA256,"source_revision_recorded":SOURCE_REVISION,"binary":BINARY,"binary_sha256":BINARY_SHA256,"root_rust_name":ROOT_RUST_NAME,"preflight_reservation_observed":{"MemAvailable_kib":53185688,"SwapFree_kib":8388604,"current_worktree_HEAD":"b87e6b73671c5bf747de1b0bf3dd324fc428912c","R289_MemoryMax":"7G","R289_MemorySwapMax":"0","running_user_services":["dbus.service","meaco-stock-bot.service"]}},indent=2)+"\n")
with (HERE/"launch.log").open("w") as out: result=subprocess.run(ssh_argv,stdout=out,stderr=subprocess.STDOUT)
print((HERE/"launch.log").read_text())
# Preserve remote failure artifacts if created, even when translator exit is nonzero.
scp=subprocess.run(["scp","-r",*SSH_OPTS,HOST+":"+REMOTE_ROOT+"/.",str(HERE)])
if scp.returncode: print("SCP_EXIT",scp.returncode,file=sys.stderr)
sys.exit(result.returncode)
