import json, hashlib, pathlib
base=pathlib.Path(__file__).resolve().parents[2]
outdir=pathlib.Path(__file__).resolve().parent

def read(rel): return (base/rel).read_bytes()
def sha(b): return hashlib.sha256(b).hexdigest()
def j(rel): return json.loads(read(rel))

r281=' .r21-scratch/r281-private-field-leaves-extract/'
r284=' .r21-scratch/r284-private-field-leaf-ordering/'
r289=' .r21-scratch/r289-aeneas-retention-candidate/'
r291=' .r21-scratch/r291-query-field-leaf-translation/'
r281=r281.strip(); r284=r284.strip(); r289=r289.strip(); r291=r291.strip()

# R281 frozen source root and LLBC.
r281_bytes=read(r281+'/R281PrivateFieldLeaves.llbc')
r281j=json.loads(r281_bytes)
r281_result=j(r281+'/result.json')
root_inspect=j(r281+'/root-body-inspection.json')
assert sha(r281_bytes)==r281_result['llbc_sha256']==root_inspect['artifact_sha256']
assert r281j['has_errors'] is False and r281_result['has_errors'] is False and root_inspect['has_errors'] is False
root_checks={}
for key,method,line in [('neg','neg',874),('mul_m31','mul_m31',927)]:
 x=root_inspect['selected_roots'][key]
 # Find literal selected body and metadata in the artifact by decoded top-level function ID.
 root_checks[key]={
  'fun_id':x['fun_id'],'method':x['method'],'source_file':x['source_file'],'source_line':x['source_line'],
  'body_kind':x['body_kind'],'item_meta_is_local':x['item_meta_is_local'],'receiver_type':x['receiver_type'],
  'body_sha256':x['body_sha256'],'line_expected':line,'exact_expected_line':x['source_line']==line,
  'structured':x['body_kind']=='Structured','llbc_function_row_present':any(f.get('def_id')==x['fun_id'] for f in r281j['translated']['fun_decls'])}
 assert x['method']==key and x['source_line']==line and x['body_kind']=='Structured'
 assert root_checks[key]['llbc_function_row_present']

# R284 changes only ordered_decls relative to exact R281 JSON.
r284_bytes=read(r284+'/R284PrivateFieldLeavesOrdered.llbc')
r284j=json.loads(r284_bytes)
a=json.loads(r281_bytes); b=json.loads(r284_bytes)
assert a['has_errors'] is False and b['has_errors'] is False
assert b['translated']['ordered_decls']
a['translated'].pop('ordered_decls',None); b['translated'].pop('ordered_decls',None)
assert a==b
ind=j(r284+'/independent-audit/independent-audit.json')
assert ind['hashes']['input']==sha(r281_bytes)
assert ind['hashes']['ordered']==sha(r284_bytes)
assert ind['changed_json_paths']==['translated.ordered_decls']
assert ind['non_order_json_identical'] and ind['all_dependencies_precede_use']
assert ind['missing_references']==[] and ind['cycles']==[]

# R289 exact one-line change, reconstruct original bytes, checksums/tree metadata/source preservation.
patch=j(r289+'/source-adapter.json')
patched=read(r289+'/src/PrePasses.ml')
old=patch['exact_old_line'].encode(); new=patch['exact_new_line'].encode()
assert patched.count(new)==1
reconstructed=patched.replace(new,old,1)
assert patched.count(old)==0
# Explicitly check checksum separately; parent hash is a file hash, not revision.
assert sha(reconstructed)==patch['parent_PrePasses_sha256']
assert sha(patched)==patch['patched_PrePasses_sha256']
assert patch['patch_change_count']=={'added':1,'removed':1}
assert patch['copy_mode'].find('no regular-file inode sharing')>=0
whole=j(r289+'/whole-tree-hashes.json')
assert whole['source_before_copy']['tree_sha256']==whole['clone_before_patch']['tree_sha256']
assert whole['shared_regular_file_inodes']==[]
assert whole['only_changed_relative_path']==['PrePasses.ml']
build=j(r289+'/build-result.json'); review=j(r289+'/lead-review.json'); host_after=j(r289+'/host-reservation-after.json')
assert build['build_exit_status']==0 and build['source_unchanged'] is True and host_after['source_unchanged'] is True
binary=read(r289+'/aeneas-r289-retention-candidate')
assert sha(binary)==build['binary_sha256']
log=read(r289+'/build.log').decode()
assert 'Maximum resident set size (kbytes): 27808' in log
assert 'Exit status: 0' in log and 'Swaps: 0' in log
cmd=j(r289+'/build-command.json');
assert cmd['systemd_limits']=={'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':'0','TasksMax':128}
assert cmd['docker_limits']['memory']=='7g' and cmd['docker_limits']['memory_swap']=='7g (equal to memory; no container swap)' and cmd['docker_limits']['pids_limit']==128
assert 'MemoryPeak=564322304' in host_after['aspisr289_slice_after']
assert 'MemorySwapPeak=0' in host_after['aspisr289_slice_after']

# R291 translation input/binary and generated declarations/helper closure.
trans=j(r291+'/generated/translation.json'); inventory=j(r291+'/inventory.json'); result=j(r291+'/result.json')
r291_funs=read(r291+'/generated/AspisAspisR291QueryFieldLeaves/Funs.lean').decode()
r291_types=read(r291+'/generated/AspisAspisR291QueryFieldLeaves/Types.lean').decode()
assert result['exit_status']==0 and result['generated'] is True
assert inventory['input_llbc_sha256']==sha(r284_bytes)
assert inventory['binary_sha256']==sha(binary)
assert inventory['namespace_used']=='AspisAspisR291QueryFieldLeaves'
assert inventory['generated_counts']=={'functions':7,'types':3,'globals':1,'trait_decls':0,'trait_impls':0}
expected={'aspis_core::field::{aspis_core::field::QM31}::neg':0,'aspis_core::field::{aspis_core::field::QM31}::mul_m31':1}
for rust,id_ in expected.items():
 f=next(f for f in trans['functions'] if f['rust_name']==rust)
 assert f['def_id']==id_ and f['is_opaque'] is False
 assert ('def aspis_core.field.QM31.'+rust.rsplit('::',1)[1]) in r291_funs
# Every translated function gets a Lean definition and exact function source identity.
for f in trans['functions']:
 assert f['lean_name'].startswith('AspisAspisR291QueryFieldLeaves.')
 assert ('def '+f['lean_name'].split('AspisAspisR291QueryFieldLeaves.',1)[1]) in r291_funs
 assert not f['is_opaque']
assert all(s in r291_funs for s in ['def aspis_core.field.CM31.neg','def aspis_core.field.M31.neg','def aspis_core.field.CM31.mul_m31','def aspis_core.field.M31.mul','def aspis_core.field.reduce_u64'])
assert all(t['lean_name'].startswith('AspisAspisR291QueryFieldLeaves.') for t in trans['types'])
assert 'structure aspis_core.field.QM31' in r291_types
assert inventory['systemd_caps']=={'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':'0','TasksMax':128}
assert inventory['metrics']['swaps']==0 and inventory['metrics']['max_rss_kib']==58960

checks={
 'R281':{'llbc_sha256':sha(r281_bytes),'has_errors':False,'roots':root_checks,'root_inspection_sha256':sha(read(r281+'/root-body-inspection.json'))},
 'R284':{'ordered_llbc_sha256':sha(r284_bytes),'only_ordered_decls_differs':True,'independent_audit_sha256':sha(read(r284+'/independent-audit/independent-audit.json')),'independent_audit_agrees':True},
 'R289':{'parent_PrePasses_sha256_reconstructed':sha(reconstructed),'patched_PrePasses_sha256':sha(patched),'one_line_change':True,'source_tree_unchanged':True,'no_shared_regular_file_inodes_recorded':True,'binary_sha256':sha(binary),'exit_status':0,'docker_cli_process_max_rss_kib':27808,'aggregate_cgroup_peak_bytes':564322304,'swap_peak_bytes':0,'caps_verified':cmd['systemd_limits']},
 'R291':{'input_llbc_sha256':sha(r284_bytes),'binary_sha256':sha(binary),'namespace':inventory['namespace_used'],'roots':inventory['requested_root_bodies'],'counts':inventory['generated_counts'],'helper_edges':inventory['helper_edges'],'opaque_functions':inventory['generated_opaque_functions'],'translation_exit_status':0,'metrics':inventory['metrics'],'lean_compiled':False}}
report={'audit':'Saved artifact chain consistency audit; read-only. No rebuild/retranslation/Lean. No semantic/source correspondence claim.','checks':checks,'all_assertions_passed':True}
path=outdir/'audit.json'; path.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
