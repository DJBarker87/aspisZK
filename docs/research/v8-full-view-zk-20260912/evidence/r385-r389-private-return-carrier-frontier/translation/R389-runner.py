#!/usr/bin/env python3
"""Translate unchanged R327 LLBC with the reviewed R385 v2 candidate; default is local preflight only."""
import argparse, datetime, hashlib, json, pathlib, shlex, subprocess, sys

HERE = pathlib.Path(__file__).resolve().parent
TASK = HERE.parent
WORKTREE = TASK.parents[1]
HOST = 'dombarker@100.108.41.90'
SSH_OPTS = ['-o', 'BatchMode=yes', '-o', 'StrictHostKeyChecking=no', '-o', 'UserKnownHostsFile=/dev/null']
REMOTE_SOURCE = '/home/dombarker/project-offloads/aspis-r327-private-batch-source-try-fold-20261002-a/R327PrivateBatchSourceTryFold.llbc'
REMOTE_BINARY = '/home/dombarker/project-offloads/aspis-r385-private-return-carrier-candidate-20261002-a/aeneas-r385-private-return-carrier-v2-candidate'
REMOTE_WORKTREE = '/home/dombarker/project-offloads/aspis-r20-r117-primal-20260930-a'
REMOTE_ROOT = '/home/dombarker/project-offloads/aspis-r389-private-batch-translation-20261002-a'
SOURCE_SHA256 = '9ed7c0ab91051ac61d812d66651680112ac26fe907faa76f9d4d2d9a14d03442'
BINARY_SHA256 = 'f12977c5acd368d268d3af9562110ab29be60d7b4055dde937d0049f85409db5'
R327_SOURCE_REVISION = 'd4bf07b08443136de0a11fc1fd932bd604586c2e'
ROOT_RUST_NAME = 'aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::batch'
ROOT_LEAN_NAME = 'AspisR389PrivateBatch.circle_norm.joined_inverse.line_norm.r110_norm.batch'
INPUT = WORKTREE / '.r21-scratch/r327-private-batch-source-try-fold/R327PrivateBatchSourceTryFold.llbc'

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def recursive_count(node, key):
    if isinstance(node, dict):
        return sum((1 if k == key else 0) + recursive_count(v, key) for k, v in node.items())
    if isinstance(node, list):
        return sum(recursive_count(v, key) for v in node)
    return 0

def local_preflight():
    raw = json.loads(INPUT.read_text())
    tr = raw['translated']
    funcs = tr['fun_decls']; types = tr['type_decls']
    option_rows = [x for x in types if isinstance(x, dict) and x['item_meta'].get('lang_item') == 'Option']
    root = [x for x in funcs if isinstance(x, dict) and x.get('def_id') == 0]
    assert sha(INPUT) == SOURCE_SHA256
    assert raw['has_errors'] is False
    assert tr['options']['start_from'] == ['crate::circle_norm::joined_inverse::line_norm::r110_norm::batch']
    assert len(funcs) == 54 and sum(x is not None for x in funcs) == 53
    assert len(types) == 29
    assert [x['def_id'] for x in option_rows] == [9, 12, 13]
    assert [x['item_meta']['lang_item'] for x in option_rows] == ['Option'] * 3
    assert all([v['name'] for v in x['kind']['Enum']] == ['None', 'Some'] for x in option_rows)
    assert len(root) == 1 and root[0]['item_meta']['is_local'] is True and root[0].get('body') not in (None, 'Opaque')
    assertions = recursive_count(raw, 'Assert')
    return {
        'source_sha256': SOURCE_SHA256, 'source_bytes': INPUT.stat().st_size,
        'has_errors': False, 'full_input_preserved': True,
        'function_rows': len(funcs), 'nonnull_function_declarations': 53,
        'type_declarations': len(types), 'global_declaration_rows': len(tr['global_decls']),
        'trait_declaration_rows': len(tr['trait_decls']), 'trait_impl_rows': len(tr['trait_impls']),
        'option_instances': {'count': len(option_rows), 'def_ids': [9, 12, 13], 'variants': ['None', 'Some']},
        'assert_variant_key_occurrences_in_json': assertions,
        'root_fun_id': 0, 'root_rust_name': ROOT_RUST_NAME, 'root_local': True, 'root_body_present': True,
        'R327_source_revision': R327_SOURCE_REVISION,
        'compiler_candidate_binary_sha256': BINARY_SHA256,
        'no_LLBC_projection_or_metadata_rewrite': True,
    }

REMOTE_SCRIPT = r'''import pathlib,hashlib,subprocess,json,re
root=pathlib.Path("@ROOT@");assert not root.exists(),f'output root exists: {root}';root.mkdir()
source=pathlib.Path("@SOURCE@");binary=pathlib.Path("@BINARY@")
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
source_sha=sha(source);binary_sha=sha(binary)
assert source_sha=="@SOURCE_SHA@",source_sha
assert binary_sha=="@BINARY_SHA@",binary_sha
raw=json.loads(source.read_text());assert raw["has_errors"] is False
tr=raw["translated"];assert tr["options"]["start_from"]==["crate::circle_norm::joined_inverse::line_norm::r110_norm::batch"]
funcs=tr["fun_decls"];types=tr["type_decls"]
assert len(funcs)==54 and sum(x is not None for x in funcs)==53
assert len(types)==29
options=[x for x in types if isinstance(x,dict) and x["item_meta"].get("lang_item")=="Option"]
assert [x["def_id"] for x in options]==[9,12,13]
assert all([v["name"] for v in x["kind"]["Enum"]]==["None","Some"] for x in options)
root_fun=next(x for x in funcs if isinstance(x,dict) and x.get("def_id")==0)
assert root_fun["item_meta"]["is_local"] is True and root_fun.get("body") not in (None,"Opaque")
root_group_index=next(i for i,x in enumerate(tr["ordered_decls"]) if x=={"Fun":{"NonRec":0}})
mem={k:v for k,v in (line.split(':',1) for line in pathlib.Path('/proc/meminfo').read_text().splitlines()) if k in ('MemTotal','MemAvailable','SwapTotal','SwapFree')}
assert int(mem['MemAvailable'].split()[0])>=24*1024*1024,mem
previous=subprocess.check_output(['systemctl','show','aspisr385.slice','-p','MemoryHigh','-p','MemoryMax','-p','MemorySwapMax','-p','MemoryCurrent','-p','MemoryPeak'],text=True)
active=subprocess.check_output(['systemctl','--user','list-units','--type=service','--state=running','--no-legend'],text=True)
containers=subprocess.check_output(['docker','ps','--no-trunc','--format','{{.ID}} {{.Names}} {{.Status}}'],text=True)
reservation={'meminfo_before':mem,'R385_slice_before':previous,'active_user_services':active,'active_docker_containers':containers,'memory_available_kib':int(mem['MemAvailable'].split()[0]),'new_scope_caps':{'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':'0','TasksMax':128},'source_sha256':source_sha,'binary_sha256':binary_sha,'R327_source_revision':'@R327_REV@','translation_launch_revision':'@LAUNCH_REV@'}
(root/'host-reservation-before.json').write_text(json.dumps(reservation,indent=2))
subprocess.run(['sudo','-n','systemctl','set-property','--runtime','aspisr389.slice','MemoryHigh=5G','MemoryMax=7G','MemorySwapMax=0','TasksMax=128'],check=True)
reservation['R389_slice_before']=subprocess.check_output(['systemctl','show','aspisr389.slice','-p','MemoryHigh','-p','MemoryMax','-p','MemorySwapMax','-p','TasksMax','-p','MemoryCurrent','-p','MemoryPeak'],text=True)
(root/'host-reservation-before.json').write_text(json.dumps(reservation,indent=2))
cmd=[str(binary),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','AspisR389PrivateBatch','-dest',str(root/'generated'),'-subdir','AspisR389PrivateBatch','-split-files','-emit-json',str(source)]
(root/'translate-command.json').write_text(json.dumps({'command':cmd,'source_sha256':source_sha,'source_revision':"@R327_REV@",'translation_launch_revision':"@LAUNCH_REV@",'binary_sha256':binary_sha,'namespace':'AspisR389PrivateBatch','sequential':True,'abort_on_error':True,'split_files':True,'emit_json':True,'input_preflight':{'has_errors':False,'function_rows':54,'nonnull_function_declarations':53,'type_declarations':29,'option_def_ids':[9,12,13],'assert_variant_key_occurrences_in_json':1},'source_gate':{'root_id':0,'root_rust_name':'@ROOT_NAME@','root_group_index':root_group_index,'root_group':{'Fun':{'NonRec':0}},'root_local':True,'root_body_present':True}},indent=2))
with (root/'translate.log').open('w') as f:r=subprocess.run(['/usr/bin/time','-v',*cmd],stdout=f,stderr=subprocess.STDOUT)
print((root/'translate.log').read_text());print('TRANSLATE_EXIT',r.returncode)
gen=root/'generated';manifest=gen/'translation.json';functions=[];root_entries=[];root_files=[];root_line=None;root_entry=None
if manifest.is_file():
 md=json.loads(manifest.read_text());functions=md.get('functions',[])
 root_entries=[f for f in functions if f.get('rust_name')=='@ROOT_NAME@' and f.get('lean_name')=='@ROOT_LEAN@']
 if len(root_entries)==1:
  root_entry=root_entries[0];lp=gen/root_entry['lean_file']
  if lp.is_file():
   lines=lp.read_text(errors='replace').splitlines();needle='def circle_norm.joined_inverse.line_norm.r110_norm.batch'
   matches=[i for i,line in enumerate(lines,1) if line==needle]
   if len(matches)==1:root_line=matches[0];root_files=[str(lp.relative_to(gen))]
templates={'functions':gen/'AspisR389PrivateBatch'/'FunsExternal_Template.lean','types':gen/'AspisR389PrivateBatch'/'TypesExternal_Template.lean'}
template_holes={k:(re.findall(r'^axiom\s+([^\s(]+)',v.read_text(errors='replace'),re.M) if v.is_file() else []) for k,v in templates.items()}
warnings=[line for line in (root/'translate.log').read_text(errors='replace').splitlines() if '[Warn' in line]
generated_hashes={str(v.relative_to(root)):hashlib.sha256(v.read_bytes()).hexdigest() for v in sorted(gen.rglob('*')) if v.is_file()} if gen.is_dir() else {}
result={'translator_exit_status':r.returncode,'generated_dir_exists':gen.is_dir(),'translation_json_exists':manifest.is_file(),'function_manifest_entries':len(functions),'required_batch_root_manifest_matches':len(root_entries),'required_batch_root_entry':root_entry,'required_batch_root_lean_files':root_files,'required_batch_root_lean_definition_line':root_line,'root_in_lean_source':root_line is not None,'external_template_axiom_holes':template_holes,'translator_warnings':warnings,'generated_file_sha256':generated_hashes,'input_declaration_inventory':{'function_rows':len(funcs),'nonnull_function_declarations':sum(x is not None for x in funcs),'type_declarations':len(types),'option_instances':len(options),'assert_variant_key_occurrences_in_json':1}}
(root/'translation-result.json').write_text(json.dumps(result,indent=2))
after={'R389_slice_after':subprocess.check_output(['systemctl','show','aspisr389.slice','-p','MemoryHigh','-p','MemoryMax','-p','MemorySwapMax','-p','TasksMax','-p','MemoryCurrent','-p','MemoryPeak','-p','MemorySwapCurrent','-p','MemorySwapPeak'],text=True),'meminfo_after':{k:v for k,v in (line.split(':',1) for line in pathlib.Path('/proc/meminfo').read_text().splitlines()) if k in ('MemTotal','MemAvailable','SwapTotal','SwapFree')}}
(root/'host-reservation-after.json').write_text(json.dumps(after,indent=2))
(root/'result.json').write_text(json.dumps({'translator_exit_status':r.returncode,'root_emission':result,'source_sha256':source_sha,'binary_sha256':binary_sha,'R327_source_revision':'@R327_REV@','translation_launch_revision':'@LAUNCH_REV@','scope':'Translation inventory only; no external template was filled or Lean compiled.'},indent=2))
raise SystemExit(r.returncode)
'''

def remote_payload(launch_revision):
    repl={
        '@ROOT@':REMOTE_ROOT,'@SOURCE@':REMOTE_SOURCE,'@BINARY@':REMOTE_BINARY,
        '@SOURCE_SHA@':SOURCE_SHA256,'@BINARY_SHA@':BINARY_SHA256,
        '@R327_REV@':R327_SOURCE_REVISION,'@LAUNCH_REV@':launch_revision,
        '@ROOT_NAME@':ROOT_RUST_NAME,'@ROOT_LEAN@':ROOT_LEAN_NAME,
    }
    out=REMOTE_SCRIPT
    for key,value in repl.items(): out=out.replace(key,value)
    return out

def plan(local, launch_revision='CAPTURED_AT_LAUNCH'):
    remote_script=remote_payload(launch_revision)
    outer=['systemd-run','--user','--wait','--collect','--pipe','--unit=aspis-r389-private-batch-translation','--working-directory='+REMOTE_WORKTREE,'-p','MemoryHigh=5G','-p','MemoryMax=7G','-p','MemorySwapMax=0','-p','TasksMax=128','python3','-c',remote_script]
    return {
        'status':'PREPARED ONLY; translation not launched',
        'source_sha256':SOURCE_SHA256,'source_path':REMOTE_SOURCE,'source_revision':R327_SOURCE_REVISION,
        'candidate_binary_sha256':BINARY_SHA256,'candidate_binary_path':REMOTE_BINARY,
        'local_preflight':local,
        'command_template':{
            'systemd_argv_prefix':outer[:15],
            'systemd_argv_template':outer[:15]+['python3','-c','<embedded remote translation script; exact hash captured in launch receipt>'],
            'translation_argv':['<R385 v2 candidate at '+REMOTE_BINARY+'>','-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','AspisR389PrivateBatch','-dest',REMOTE_ROOT+'/generated','-subdir','AspisR389PrivateBatch','-split-files','-emit-json',REMOTE_SOURCE],
            'namespace':'AspisR389PrivateBatch','sequential':True,'abort_on_error':True,'split_files':True,'emit_json':True,
            'full_source_input':True,'no_LLBC_projection_or_metadata_rewrite':True,
        },
        'systemd_caps':{'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':'0','TasksMax':128},
        'docker_not_used_for_translation':'The pinned binary executes directly in the systemd/cgroup scope, following R330.',
        'expected_preflight':'Exact source and candidate binary hashes; has_errors false; complete raw declaration counts; root body present; all three Option rows; available memory >=24 GiB.',
        'translation_output_review_gate':'Inspect root output, warnings, and all external-template holes before any Lean source is promoted or compiled.',
        'boundary':'This run inventories translation only; no templates are filled, no Lean proof is claimed, and no source semantics/security claim is made.',
    }

parser=argparse.ArgumentParser()
parser.add_argument('--lead-reviewed-r389-translation',action='store_true',help='launch after lead reviews the exact R389 plan and authorizes this translation')
args=parser.parse_args()
local=local_preflight()
if not args.lead_reviewed_r389_translation:
    print(json.dumps(plan(local),indent=2))
    raise SystemExit(0)

launch_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=WORKTREE,text=True).strip()
assert len(launch_revision)==40 and all(c in '0123456789abcdef' for c in launch_revision),launch_revision
stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
history=TASK/'r389-launch-history'/('launch-'+launch_revision[:12]+'-'+stamp)
history.mkdir(parents=True,exist_ok=False)
payload=remote_payload(launch_revision)
payload_path=history/'remote_translate.py';payload_path.write_text(payload)
payload_sha=sha(payload_path)
outer=['systemd-run','--user','--wait','--collect','--pipe','--unit=aspis-r389-private-batch-translation','--working-directory='+REMOTE_WORKTREE,'-p','MemoryHigh=5G','-p','MemoryMax=7G','-p','MemorySwapMax=0','-p','TasksMax=128','python3','-c',payload]
ssh_argv=['ssh',*SSH_OPTS,HOST,shlex.join(outer)]
receipt={'launch_revision':launch_revision,'timestamp_utc':stamp,'R327_source_revision':R327_SOURCE_REVISION,'source_sha256':SOURCE_SHA256,'candidate_binary_sha256':BINARY_SHA256,'remote_payload_sha256':payload_sha,'local_preflight':local,'ssh_argv':ssh_argv,'systemd_argv':outer,'caps':{'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':'0','TasksMax':128},'scope':'Translation inventory only; no Lean compile.'}
(history/'launch.json').write_text(json.dumps(receipt,indent=2)+'\n')
with (history/'launch.log').open('w') as log:proc=subprocess.run(ssh_argv,stdout=log,stderr=subprocess.STDOUT)
receipt['launcher_exit_status']=proc.returncode
(history/'launch-result.json').write_text(json.dumps(receipt,indent=2)+'\n')
copy=TASK/'r389-translation-output'/('output-'+launch_revision[:12]+'-'+stamp);copy.mkdir(parents=True,exist_ok=False)
scp=subprocess.run(['scp','-r',*SSH_OPTS,HOST+':'+REMOTE_ROOT+'/.',str(copy)])
receipt['scp_exit_status']=scp.returncode
(history/'launch-result.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({'translator_exit_status':proc.returncode,'scp_exit_status':scp.returncode,'history':str(history),'output_copy':str(copy),'remote_payload_sha256':payload_sha},indent=2))
raise SystemExit(proc.returncode if proc.returncode else scp.returncode)
