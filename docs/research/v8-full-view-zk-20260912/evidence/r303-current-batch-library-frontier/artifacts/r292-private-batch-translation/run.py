#!/usr/bin/env python3
"""Translate the exact original R283 LLBC once in the pinned capped host."""
import hashlib, json, pathlib, shlex, subprocess, sys

HERE = pathlib.Path(__file__).resolve().parent
HOST = "dombarker@100.108.41.90"
SSH_OPTS = ["-o", "BatchMode=yes", "-o", "StrictHostKeyChecking=no", "-o", "UserKnownHostsFile=/dev/null"]
REMOTE_WORKTREE = "/home/dombarker/project-offloads/aspis-r20-r117-primal-20260930-a"
REMOTE_ROOT = "/home/dombarker/project-offloads/aspis-r292-private-batch-translation-20261002-a"
SOURCE = "/home/dombarker/project-offloads/aspis-r283-private-norm-batch-extract-20261002-a/R283PrivateNormBatch.llbc"
BINARY = "/home/dombarker/project-offloads/aspis-return-continuation-20261002-a/aeneas-return-continuation"
SOURCE_SHA256 = "999fdb4f5a034faf9d4aa11c7a44851b9c79f471d76ae6afb3b92aed0767c8d5"
BINARY_SHA256 = "63b04a88532b8fb0aaa0d274881b5cacf00bc4f449243ece905178f0de9cc495"
SOURCE_REVISION = "380c7d46c9719dcfcab601fac2607861d47dee02"
ROOT_RUST_NAME = "aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::batch"

REMOTE_SCRIPT = r'''import pathlib,hashlib,subprocess,json
root=pathlib.Path("@REMOTE_ROOT@");assert not root.exists(),f'output root exists: {root}';root.mkdir()
source=pathlib.Path("@SOURCE@");binary=pathlib.Path("@BINARY@")
source_sha=hashlib.sha256(source.read_bytes()).hexdigest();binary_sha=hashlib.sha256(binary.read_bytes()).hexdigest()
assert source_sha=="@SOURCE_SHA@",source_sha
assert binary_sha=="@BINARY_SHA@",binary_sha
raw=json.loads(source.read_text()); assert raw["has_errors"] is False
tr=raw["translated"]; assert tr["options"]["start_from"]==["crate::circle_norm::joined_inverse::line_norm::r110_norm::batch"]
root_fun=next(x for x in tr["fun_decls"] if isinstance(x,dict) and x.get("def_id")==0)
assert root_fun["item_meta"]["is_local"] is True and root_fun.get("body") not in (None,"Opaque")
assert tr["ordered_decls"][107]=={"Fun":{"NonRec":0}}
mem={k:v for k,v in (line.split(':',1) for line in pathlib.Path('/proc/meminfo').read_text().splitlines()) if k in ('MemTotal','MemAvailable','SwapTotal','SwapFree')}
assert int(mem['MemAvailable'].split()[0])>=24*1024*1024,mem
r289=subprocess.check_output(['systemctl','show','aspisr289.slice','-p','MemoryHigh','-p','MemoryMax','-p','MemorySwapMax','-p','MemoryCurrent'],text=True)
existing=subprocess.check_output(['systemctl','--user','list-units','--type=service','--state=running','--no-legend'],text=True)
reservation={'meminfo_before':mem,'r289_slice_before':r289,'active_user_services':existing,'memory_available_kib':int(mem['MemAvailable'].split()[0]),'reserved_target_MemoryMax':'R289 7G plus R292 7G = 14G; current MemAvailable checked >= 24GiB','caps':{'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':'0','TasksMax':128},'source_revision_recorded':'@SOURCE_REV@','source_revision_basis':'current preparation worktree revision; R283 LLBC is pinned by SHA and does not derive its revision from this field','source_sha256':source_sha,'binary_sha256':binary_sha}
(root/'host-reservation-before.json').write_text(json.dumps(reservation,indent=2))
subprocess.run(['sudo','-n','systemctl','set-property','--runtime','aspisr292.slice','MemoryHigh=5G','MemoryMax=7G','MemorySwapMax=0','TasksMax=128'],check=True)
reservation['r292_slice_before']=subprocess.check_output(['systemctl','show','aspisr292.slice','-p','MemoryHigh','-p','MemoryMax','-p','MemorySwapMax','-p','TasksMax','-p','MemoryCurrent','-p','MemoryPeak'],text=True)
(root/'host-reservation-before.json').write_text(json.dumps(reservation,indent=2))
cmd=[str(binary),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','AspisR292PrivateBatch','-dest',str(root/'generated'),'-subdir','AspisR292PrivateBatch','-split-files','-emit-json',str(source)]
(root/'translate-command.json').write_text(json.dumps({'command':cmd,'source_sha256':source_sha,'source_revision_recorded':'@SOURCE_REV@','binary_sha256':binary_sha,'namespace':'AspisR292PrivateBatch','sequential':True,'abort_on_error':True,'split_files':True,'emit_json':True,'source_gate':{'has_errors':raw['has_errors'],'root_id':0,'root_rust_name':'@ROOT_NAME@','root_group_index':107,'root_group':{'Fun':{'NonRec':0}},'root_local':True,'root_body_present':True}},indent=2))
with (root/'translate.log').open('w') as f:r=subprocess.run(['/usr/bin/time','-v',*cmd],stdout=f,stderr=subprocess.STDOUT)
print((root/'translate.log').read_text());print('TRANSLATE_EXIT',r.returncode)
gen=root/'generated';manifest=gen/'translation.json';functions=[];root_emitted=False;lean_root_occurrences=[]
if manifest.is_file():
 md=json.loads(manifest.read_text());functions=md.get('functions',[]);root_emitted=any(f.get('rust_name')=='@ROOT_NAME@' for f in functions)
for lp in gen.rglob('*.lean') if gen.exists() else []:
 txt=lp.read_text(errors='replace')
 if 'AspisR292PrivateBatch.aspis_v8_performance_host.circle_norm.joined_inverse.line_norm.r110_norm.batch' in txt: lean_root_occurrences.append(str(lp.relative_to(gen)))
metrics={'translator_exit_status':r.returncode,'generated_dir_exists':gen.is_dir(),'translation_json_exists':manifest.is_file(),'function_manifest_entries':len(functions),'required_batch_root_emitted_in_translation_manifest':root_emitted,'required_batch_root_lean_files':sorted(set(lean_root_occurrences)),'root_in_lean_source':bool(lean_root_occurrences)}
(root/'translation-result.json').write_text(json.dumps(metrics,indent=2))
after={'r292_slice_after':subprocess.check_output(['systemctl','show','aspisr292.slice','-p','MemoryHigh','-p','MemoryMax','-p','MemorySwapMax','-p','TasksMax','-p','MemoryCurrent','-p','MemoryPeak','-p','MemorySwapCurrent','-p','MemorySwapPeak'],text=True),'meminfo_after':{k:v for k,v in (line.split(':',1) for line in pathlib.Path('/proc/meminfo').read_text().splitlines()) if k in ('MemTotal','MemAvailable','SwapTotal','SwapFree')}}
(root/'host-reservation-after.json').write_text(json.dumps(after,indent=2))
(root/'result.json').write_text(json.dumps({'translator_exit_status':r.returncode,'root_emission':metrics,'source_sha256':source_sha,'binary_sha256':binary_sha,'source_revision_recorded':'@SOURCE_REV@'},indent=2))
raise SystemExit(r.returncode)
'''

def sub(src, mapping):
    for k,v in mapping.items(): src=src.replace(k,v)
    return src
mapping={"@REMOTE_ROOT@":REMOTE_ROOT,"@SOURCE@":SOURCE,"@BINARY@":BINARY,"@SOURCE_SHA@":SOURCE_SHA256,"@BINARY_SHA@":BINARY_SHA256,"@SOURCE_REV@":SOURCE_REVISION,"@ROOT_NAME@":ROOT_RUST_NAME}
remote_script=sub(REMOTE_SCRIPT,mapping)
outer=["systemd-run","--user","--wait","--collect","--pipe","--unit=aspis-r292-private-batch-translation","--working-directory="+REMOTE_WORKTREE,"-p","MemoryHigh=5G","-p","MemoryMax=7G","-p","MemorySwapMax=0","-p","TasksMax=128","python3","-c",remote_script]
ssh_argv=["ssh",*SSH_OPTS,HOST,shlex.join(outer)]
(HERE/"launch.json").write_text(json.dumps({"ssh_argv":ssh_argv,"systemd_argv":outer,"caps":{"MemoryHigh":"5G","MemoryMax":"7G","MemorySwapMax":"0","TasksMax":128},"remote_worktree":REMOTE_WORKTREE,"remote_output_root":REMOTE_ROOT,"source":SOURCE,"source_sha256":SOURCE_SHA256,"source_revision_recorded":SOURCE_REVISION,"binary":BINARY,"binary_sha256":BINARY_SHA256,"root_rust_name":ROOT_RUST_NAME,"preflight_reservation_observed":{"MemAvailable_kib":53878932,"R289_MemoryMax":"7G","R289_MemorySwapMax":"0","running_user_services":["dbus.service","meaco-stock-bot.service"]}},indent=2)+"\n")
with (HERE/"launch.log").open("w") as out: result=subprocess.run(ssh_argv,stdout=out,stderr=subprocess.STDOUT)
print((HERE/"launch.log").read_text())
# Preserve remote failure artifacts if created, even when translator exit is nonzero.
scp=subprocess.run(["scp","-r",*SSH_OPTS,HOST+":"+REMOTE_ROOT+"/.",str(HERE)])
if scp.returncode: print("SCP_EXIT",scp.returncode,file=sys.stderr)
sys.exit(result.returncode)
