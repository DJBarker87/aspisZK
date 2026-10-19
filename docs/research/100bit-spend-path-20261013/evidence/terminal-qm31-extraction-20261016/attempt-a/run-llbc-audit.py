import json,hashlib,pathlib,subprocess
base=pathlib.Path('/home/dombarker/project-offloads/aspis-r1-terminal-extraction-20261016')
att=base/'attempt-a'; out=att/'output'; rec=att/'receipts'
llbc=out/'charon-a/Terminal.llbc'; d=json.load(open(llbc)); t=d['translated']
def pname(meta):
    parts=[]
    for e in (meta or {}).get('name') or []:
        if isinstance(e,dict) and 'Ident' in e: parts.append(e['Ident'][0])
        elif isinstance(e,dict) and 'Impl' in e: parts.append('<impl>')
        elif isinstance(e,dict): parts.append(next(iter(e)))
    return '::'.join(parts)
def sdata(meta):
    x=(meta or {}).get('span') or {}
    return x.get('data') or {}
files={x['id']:((x.get('name') or {}).get('Local',str(x.get('name')))) for x in t['files']}
funcs=[]; opaque=[]
for f in t['fun_decls']:
    if not isinstance(f,dict): continue
    m=f.get('item_meta') or {}; n=pname(m); s=sdata(m); body=f.get('body')
    kind=next(iter(body)) if isinstance(body,dict) and body else None
    row={'name':n,'source_file':files.get(s.get('file_id')),'line_start':(s.get('beg') or {}).get('line'),'line_end':(s.get('end') or {}).get('line'),'local':m.get('is_local'),'opacity':m.get('opacity'),'body_kind':kind,'source_text_sha256':hashlib.sha256((m.get('source_text') or '').encode()).hexdigest()}
    if n.split('::')[-1] in {'terminal_qm31_probe','terminal_qm31','terminal_parts','composition_parts'}: funcs.append(row)
    if m.get('opacity')!='Transparent' or not m.get('is_local',False): opaque.append(row)
types=[]
for f in t['type_decls']:
    if not isinstance(f,dict): continue
    m=f.get('item_meta') or {}; n=pname(m); s=sdata(m)
    if any(x in n.lower() for x in ['m31','qm31','cm31','preparedqm31multiplier','challenges']):
        types.append({'name':n,'source_file':files.get(s.get('file_id')),'line_start':(s.get('beg') or {}).get('line'),'line_end':(s.get('end') or {}).get('line'),'local':m.get('is_local'),'opacity':m.get('opacity')})
res={'llbc_sha256':hashlib.sha256(llbc.read_bytes()).hexdigest(),'llbc_bytes':llbc.stat().st_size,'charon_version':d.get('charon_version'),'has_errors':d.get('has_errors'),'options':{k:t['options'].get(k) for k in ['mir','sysroot','start_from','monomorphize','monomorphize_mut','preset','no_reorder_decls']},'counts':{'functions':len(t['fun_decls']),'types':len(t['type_decls']),'globals':len(t['global_decls']),'traits':len(t['trait_decls']),'trait_impls':len(t['trait_impls']),'opaque_or_external_functions':len(opaque),'files':len(t['files'])},'target_functions':funcs,'field_type_declarations':types,'opaque_or_external_names':[x['name'] for x in opaque]}
path=out/'llbc-target-audit.json'; json.dump(res,open(path,'w'),indent=2)
# compact provenance from tool-build receipts
charon_root=pathlib.Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016')
cr=json.load(open(charon_root/'charon-build-a/receipt.json')); ar=json.load(open(charon_root/'aeneas-build-a/receipt.json'))
provenance={'charon':{'binary':cr['binaries']['charon'],'driver':cr['binaries']['charon-driver'],'version':d.get('charon_version'),'source_archives':cr['source_archive_pins'],'dependency_pins_sha256':cr['dependency_pins_sha256'],'build_receipt':{'exit_status':cr['exit_status'],'wall_seconds':cr['wall_seconds'],'cgroup_memory_peak_bytes':cr['sampled_cgroup_peak_bytes'],'peak_process_rss_kib':cr['peak_process_rss_kib'],'process_swaps':cr['process_swaps'],'cgroup_limits':cr['limits']}},'aeneas':{'binary_sha256':ar['binary_sha256'],'version':(att/'receipts/aeneas-a/aeneas-version.txt').read_text().strip(),'source_archives':ar['source_archives'],'container_image':ar['image'],'source_build_receipt':{'exit_status':ar['exit_status'],'wall_seconds':ar['wall_seconds'],'cgroup_memory_peak_bytes':ar['sampled_cgroup_peak_bytes'],'peak_process_rss_kib':ar['peak_process_rss_kib'],'process_swaps':ar['process_swaps'],'cgroup_limits':ar['limits']}}}
json.dump(provenance,open(rec/'tool-provenance.json','w'),indent=2)
