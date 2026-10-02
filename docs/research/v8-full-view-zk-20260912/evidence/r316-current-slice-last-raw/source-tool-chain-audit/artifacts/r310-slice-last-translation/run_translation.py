#!/usr/bin/env python3
"""Run the lead-authorized exact R309 LLBC translation in the capped host scope."""
import hashlib, json, pathlib, shlex, subprocess, sys

HERE=pathlib.Path(__file__).resolve().parent
HOST='dombarker@100.108.41.90'
SSH=['-o','BatchMode=yes','-o','StrictHostKeyChecking=no','-o','UserKnownHostsFile=/dev/null']
LOCAL_SOURCE=HERE.parent/'r309-slice-last-with-length-projection/R309SliceLastWithLengthProjection.llbc'
SOURCE_SHA='9264aea58bf430b023ed8124bf8737ef6943e97230f08aa7982648f4f7557421'
BINARY='/home/dombarker/project-offloads/aspis-r289-retention-candidate-20261002-a/aeneas-r289-retention-candidate'
BINARY_SHA='3c741510837e33e0debca5798fb46ae81861ec06d5d561b7975b16f5705e42e9'
REV='04d7d1b635ddb7c9af2ee3e2df3cdb68ae68bb43'
WORKTREE='/home/dombarker/project-offloads/aspis-r20-r117-primal-20260930-a'
REMOTE_ROOT='/home/dombarker/project-offloads/aspis-r310-slice-last-translation-20261002-a'
REMOTE_SOURCE=REMOTE_ROOT+'/R309SliceLastWithLengthProjection.llbc'
ROOT_NAME='core::slice::{Impl}::last'
assert hashlib.sha256(LOCAL_SOURCE.read_bytes()).hexdigest()==SOURCE_SHA

# Record a fresh host reservation check before transfer or launching any work.
pre_cmd="cat /proc/meminfo | grep -E '^(MemTotal|MemAvailable|SwapTotal|SwapFree):'; systemctl show aspisr289.slice -p MemoryHigh -p MemoryMax -p MemorySwapMax -p MemoryCurrent; systemctl --user list-units --type=service --state=running --no-legend; df -h /home/dombarker/project-offloads; sha256sum "+shlex.quote(BINARY)
pre=subprocess.run(['ssh',*SSH,HOST,pre_cmd],text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,check=True)
(HERE/'host-reservation-before.txt').write_text(pre.stdout)
assert 'MemAvailable:' in pre.stdout
available=int(next(x.split()[1] for x in pre.stdout.splitlines() if x.startswith('MemAvailable:')))
assert available>=24*1024*1024, f'insufficient MemAvailable KiB: {available}'
assert BINARY_SHA in pre.stdout, 'remote pinned binary hash mismatch'

# Stage exact input under the new, task-specific remote directory.
mk="test ! -e "+shlex.quote(REMOTE_ROOT)+" && mkdir -p "+shlex.quote(REMOTE_ROOT)
subprocess.run(['ssh',*SSH,HOST,mk],check=True)
subprocess.run(['scp','-q',*SSH,str(LOCAL_SOURCE),HOST+':'+REMOTE_SOURCE],check=True)

remote_script=r'''import pathlib,hashlib,subprocess,json,re
root=pathlib.Path("@ROOT@"); source=pathlib.Path("@SOURCE@"); binary=pathlib.Path("@BINARY@"); gen=root/'generated'
assert root.is_dir() and not gen.exists()
sha=lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(source)=="@SOURCE_SHA@",sha(source)
assert sha(binary)=="@BINARY_SHA@",sha(binary)
raw=json.loads(source.read_text()); assert raw['has_errors'] is False
tr=raw['translated']; assert tr['ordered_decls']==[{'Type':{'NonRec':9}},{'Fun':{'NonRec':5}},{'Fun':{'NonRec':12}}]
len_rows=[x for x in tr['fun_decls'] if isinstance(x,dict) and x.get('item_meta',{}).get('lang_item')=='slice_len_fn']; assert len(len_rows)==1 and len_rows[0]['def_id']==5
row=next(x for x in tr['fun_decls'] if isinstance(x,dict) and x.get('def_id')==12)
assert row['item_meta']['is_local'] is False and row.get('body') not in (None,'Opaque')
root_group_index=next(i for i,x in enumerate(tr['ordered_decls']) if x=={'Fun':{'NonRec':12}})
mem={k:v for k,v in (line.split(':',1) for line in pathlib.Path('/proc/meminfo').read_text().splitlines()) if k in ('MemTotal','MemAvailable','SwapTotal','SwapFree')}
assert int(mem['MemAvailable'].split()[0])>=24*1024*1024,mem
r289=subprocess.check_output(['systemctl','show','aspisr289.slice','-p','MemoryHigh','-p','MemoryMax','-p','MemorySwapMax','-p','MemoryCurrent'],text=True)
existing=subprocess.check_output(['systemctl','--user','list-units','--type=service','--state=running','--no-legend'],text=True)
reservation={'meminfo_before':mem,'r289_slice_before':r289,'active_user_services':existing,'memory_available_kib':int(mem['MemAvailable'].split()[0]),'reserved_target_MemoryMax':'R289 7G plus R310 7G = 14G; current MemAvailable checked >= 24GiB','caps':{'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':'0','TasksMax':128},'source_revision_recorded':'@REV@','source_sha256':sha(source),'binary_sha256':sha(binary)}
(root/'host-reservation-before.json').write_text(json.dumps(reservation,indent=2))
subprocess.run(['sudo','-n','systemctl','set-property','--runtime','aspisr310.slice','MemoryHigh=5G','MemoryMax=7G','MemorySwapMax=0','TasksMax=128'],check=True)
reservation['r310_slice_before']=subprocess.check_output(['systemctl','show','aspisr310.slice','-p','MemoryHigh','-p','MemoryMax','-p','MemorySwapMax','-p','TasksMax','-p','MemoryCurrent','-p','MemoryPeak'],text=True)
(root/'host-reservation-before.json').write_text(json.dumps(reservation,indent=2))
cmd=[str(binary),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','AspisR310SliceLast','-dest',str(gen),'-subdir','AspisR310SliceLast','-split-files','-emit-json',str(source)]
(root/'translate-command.json').write_text(json.dumps({'command':cmd,'source_sha256':sha(source),'source_revision_recorded':'@REV@','binary_sha256':sha(binary),'namespace':'AspisR310SliceLast','sequential':True,'abort_on_error':True,'split_files':True,'emit_json':True,'source_gate':{'has_errors':raw['has_errors'],'ordered_decls':tr['ordered_decls'],'root_id':12,'root_rust_name':'@ROOT_NAME@','root_group_index':root_group_index,'root_group':{'Fun':{'NonRec':12}},'root_local':False,'root_body_present':True}},indent=2))
with (root/'translate.log').open('w') as f: result=subprocess.run(['/usr/bin/time','-v',*cmd],stdout=f,stderr=subprocess.STDOUT)
print((root/'translate.log').read_text()); print('TRANSLATE_EXIT',result.returncode)
manifest=gen/'translation.json'; functions=[]; matches=[]; entry=None; root_line=None; root_files=[]
if manifest.is_file():
 md=json.loads(manifest.read_text()); functions=md.get('functions',[])
 matches=[f for f in functions if f.get('rust_name')=='@ROOT_NAME@']
 if len(matches)==1:
  entry=matches[0]; lp=gen/entry['lean_file']
  if lp.is_file():
   ls=lp.read_text(errors='replace').splitlines(); lean_name=entry.get('lean_name',''); leaf=lean_name.removeprefix('AspisR310SliceLast.'); needle='def '+leaf
   hits=[i for i,l in enumerate(ls,1) if l.strip()==needle]
   if len(hits)==1: root_line=hits[0]; root_files=[str(lp.relative_to(gen))]
templates={'functions':gen/'AspisR310SliceLast'/'FunsExternal_Template.lean','types':gen/'AspisR310SliceLast'/'TypesExternal_Template.lean'}
holes={k:(re.findall(r'^axiom\s+([^\s(]+)',p.read_text(errors='replace'),re.M) if p.is_file() else []) for k,p in templates.items()}
warns=[l for l in (root/'translate.log').read_text(errors='replace').splitlines() if '[Warn' in l]
hashes={str(p.relative_to(root)):sha(p) for p in sorted(gen.rglob('*')) if p.is_file()} if gen.is_dir() else {}
metrics={'translator_exit_status':result.returncode,'generated_dir_exists':gen.is_dir(),'translation_json_exists':manifest.is_file(),'function_manifest_entries':len(functions),'root_manifest_matches':len(matches),'root_entry':entry,'root_lean_files':root_files,'root_lean_name':(entry.get('lean_name') if entry else None),'root_lean_definition_line':root_line,'root_definition_present':root_line is not None,'external_template_axiom_holes':holes,'translator_warnings':warns,'generated_file_sha256':hashes}
(root/'translation-result.json').write_text(json.dumps(metrics,indent=2))
after={'r310_slice_after':subprocess.check_output(['systemctl','show','aspisr310.slice','-p','MemoryHigh','-p','MemoryMax','-p','MemorySwapMax','-p','TasksMax','-p','MemoryCurrent','-p','MemoryPeak','-p','MemorySwapCurrent','-p','MemorySwapPeak'],text=True),'meminfo_after':{k:v for k,v in (line.split(':',1) for line in pathlib.Path('/proc/meminfo').read_text().splitlines()) if k in ('MemTotal','MemAvailable','SwapTotal','SwapFree')}}
(root/'host-reservation-after.json').write_text(json.dumps(after,indent=2))
(root/'result.json').write_text(json.dumps({'translator_exit_status':result.returncode,'root_emission':metrics,'source_sha256':sha(source),'binary_sha256':sha(binary),'source_revision_recorded':'@REV@','scope':'Focused translation only. No Lean compilation, templates filled, or source-semantics claim.'},indent=2))
raise SystemExit(result.returncode)
'''
for k,v in {'@ROOT@':REMOTE_ROOT,'@SOURCE@':REMOTE_SOURCE,'@BINARY@':BINARY,'@SOURCE_SHA@':SOURCE_SHA,'@BINARY_SHA@':BINARY_SHA,'@REV@':REV,'@ROOT_NAME@':ROOT_NAME}.items(): remote_script=remote_script.replace(k,v)
outer=['systemd-run','--user','--wait','--collect','--pipe','--unit=aspis-r310-slice-last-translation','--working-directory='+WORKTREE,'-p','MemoryHigh=5G','-p','MemoryMax=7G','-p','MemorySwapMax=0','-p','TasksMax=128','python3','-c',remote_script]
ssh_argv=['ssh',*SSH,HOST,shlex.join(outer)]
(HERE/'launch.json').write_text(json.dumps({'ssh_argv':ssh_argv,'systemd_argv':outer,'caps':{'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':'0','TasksMax':128},'remote_worktree':WORKTREE,'remote_root':REMOTE_ROOT,'source':str(LOCAL_SOURCE),'source_sha256':SOURCE_SHA,'binary':BINARY,'binary_sha256':BINARY_SHA,'source_revision_recorded':REV,'root_rust_name':ROOT_NAME,'host_reservation_preflight':pre.stdout},indent=2)+'\n')
with (HERE/'launch.log').open('w') as log: run=subprocess.run(ssh_argv,stdout=log,stderr=subprocess.STDOUT,text=True)
print((HERE/'launch.log').read_text())
scp=subprocess.run(['scp','-r',*SSH,HOST+':'+REMOTE_ROOT+'/.',str(HERE)])
if scp.returncode: print('SCP_EXIT',scp.returncode,file=sys.stderr)
sys.exit(run.returncode)
