#!/usr/bin/env python3
"""Independent custody/manifest/metric audit for the saved R439 translation."""
import hashlib,json,pathlib,re,subprocess

ROOT=pathlib.Path(__file__).resolve().parents[3]
RUN=ROOT/'.r21-scratch/r439-closure-execution-preflight/translation-runner'
OUT=RUN/'output/54e804310fa3-20261003T050407Z'
R174=ROOT/'docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/R174GammaBatchStep.lean'
EXPECTED={
 'input_sha256':'d28419f408e6bab79c80859db37e137f4ab62b6bd73c7c5a5d909582308a75b9',
 'binary_sha256':'eadb205fc1e00cf7e32197dd7cbbbd82aa42b59442d8f186cfdca7c8fdca9b01',
 'source_revision':'54e804310fa3f8dbf4dfc0afe4343ba94247542e',
 'payload_sha256':'7e6e26cb485825e0e538c757ac66ea9cf593eef6d3988e26a1c2ee02aabdd15f',
}

def sha(b): return hashlib.sha256(b).hexdigest()
def readj(p): return json.loads(p.read_text())
def normal_body(text):
    # Normalize only Aeneas' module qualification for field calls/types and formatting whitespace.
    return re.sub(r'\s+',' ',text.replace('aspis_core.field.','field.')).strip()

def declaration_parts(block, name_pattern):
    m=re.search(name_pattern+r'(?P<header>.*?)\:= do\n(?P<body>.*)$',block,re.S)
    assert m, ('could not split callback declaration', block[:160])
    return m.group('header'),m.group('body')

def main():
    result=readj(OUT/'result.json'); trans=readj(OUT/'translation-result.json')
    cmd=readj(OUT/'translate-command.json'); launch=readj(RUN/'launch-history/54e804310fa3-20261003T050407Z/launch.json')
    launched=readj(RUN/'launch-history/54e804310fa3-20261003T050407Z/launch-result.json')
    collected=readj(RUN/'launch-history/54e804310fa3-20261003T050407Z/collection-status.json')
    assert result['translator_exit_status']==0 and result['gnu_time_exit_status']==0
    assert trans['translator_exit_status']==0 and trans['generated_dir_exists'] and trans['translation_json_exists']
    for k,v in EXPECTED.items():
        actual={'input_sha256':result['input_sha256'],'binary_sha256':result['binary_sha256'],'source_revision':result['source_revision'],'payload_sha256':launch['remote_payload_sha256']}[k]
        assert actual==v,(k,actual,v)
    assert launched['launcher_exit_status']==0 and collected['exit_status']==0
    assert launch['input_sha256']==EXPECTED['input_sha256'] and launch['binary_sha256']==EXPECTED['binary_sha256']
    assert launch['source_revision']==EXPECTED['source_revision'] and launch['projection_source_revision']=='e0d03f10e3834608a06d3b62af3e2f7abfba8c4a'
    assert launch['unit']=='aspis-r439-generic-gamma-translation'
    assert launch['caps']=={'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':'0','TasksMax':128,'RuntimeMaxSec':'600s'}
    assert result['namespace']=='AspisR439GenericGamma' and result['manifest_binding_gate_passed'] is True
    assert trans['manifest_root_def_id_284_matches']==1 and trans['manifest_impl47_trait9_matches']==1
    assert trans['source_ordered_fun284_and_traitimpl47_asserted'] is True
    assert trans['manifest_source_root_impl47_trait9_method0_asserted'] is True
    assert trans['warning_lines']==[] and trans['external_template_axiom_names']=={}
    gen=OUT/'generated'; manifest=readj(gen/'translation.json')
    root_rows=[f for f in manifest['functions'] if f['def_id']==284]
    impl_rows=[i for i in manifest['trait_impls'] if i['def_id']==47]
    assert len(root_rows)==len(impl_rows)==1
    root=root_rows[0]; impl=impl_rows[0]
    assert root['is_opaque'] is False and root['lean_file']=='AspisR439GenericGamma/Funs.lean'
    assert impl['impl_trait_def_id']==9 and impl['impl_trait_rust_name']=='core::ops::function::FnMut'
    assert manifest['aeneas_version']=='aspis-r425-unit-constant-candidate' and manifest['charon_version']=='0.1.223'
    assert (manifest['crate']=='aspis_v8_performance_host')
    assert len(manifest['functions'])==20 and len(manifest['types'])==6 and len(manifest['trait_impls'])==2
    assert len(manifest['trait_decls'])==0 and len(manifest['globals'])==2
    assert all(not f['is_opaque'] for f in manifest['functions'])
    expected_files=trans['generated_file_sha256']
    found={str(p.relative_to(OUT)):sha(p.read_bytes()) for p in sorted(gen.rglob('*')) if p.is_file()}
    assert found==expected_files,(found,expected_files)
    for name,h in expected_files.items(): assert sha((OUT/name).read_bytes())==h
    assert set(expected_files)=={'generated/AspisR439GenericGamma/Funs.lean','generated/AspisR439GenericGamma/Types.lean','generated/translation.json'}
    assert not any(p.name in {'FunsExternal_Template.lean','TypesExternal_Template.lean'} for p in gen.rglob('*') if p.is_file())
    axiom_lines=[]
    for lean_file in gen.rglob('*.lean'):
        for line_number,line in enumerate(lean_file.read_text().splitlines(),1):
            if re.match(r'\s*axiom\s+',line): axiom_lines.append({'file':str(lean_file.relative_to(gen)),'line':line_number,'text':line.strip()})
    assert axiom_lines==[]
    funs=(gen/'AspisR439GenericGamma/Funs.lean').read_text(); types=(gen/'AspisR439GenericGamma/Types.lean').read_text()
    generated_match=re.search(r'def\s+freeze\.closure_2\.closure\.Insts\.CoreOpsFunctionFnMutPairQM31SharedQM31QM31\.call_mut\b.*?\:= do\n.*?(?=\n\n/-- )',funs,re.S)
    old_text=R174.read_text()
    raw_match=re.search(r'def\s+rawCallMut\b.*?\:= do\n.*?(?=\n\ntheorem rawCallMut_closed\b)',old_text,re.S)
    assert generated_match and raw_match
    generated_decl=generated_match.group(0); old_decl=raw_match.group(0)
    gen_head,gen_body=declaration_parts(generated_decl,r'freeze\.closure_2\.closure\.Insts\.CoreOpsFunctionFnMutPairQM31SharedQM31QM31\.call_mut\b')
    old_head,old_body=declaration_parts(old_decl,r'rawCallMut\b')
    normalized_generated_body=normal_body(gen_body)
    normalized_old_body=normal_body(old_body)
    assert normalized_generated_body==normalized_old_body, 'callback body differs beyond field namespace qualification/formatting whitespace'
    # Signature audit records rather than hides the generated extra grouping parens around a product type.
    def normalized_head(h): return re.sub(r'\s+',' ',h.replace('aspis_core.field.','field.')).strip()
    norm_gen_head=normalized_head(gen_head); norm_old_head=normalized_head(old_head)
    # Verify full native callback and the generated FnOnce bridge/impl dictionaries remain available in the saved output.
    assert 'freeze.closure_2.closure.Insts.CoreOpsFunctionFnOncePairQM31SharedQM31QM31.call_once' in funs
    assert 'core.ops.function.FnOnce' in funs and 'core.ops.function.FnMut' in funs
    assert 'FnOnceInst :=' in funs and 'call_mut :=' in funs
    assert 'structure aspis_core.field.QM31 where' in types
    assert 'def freeze.closure_2.closure := aspis_core.field.QM31 × aspis_core.field.QM31' in types
    assert '__aeneas_pending_return_87' in types
    gnu=(OUT/'gnu-time.txt').read_text()
    elapsed=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\):\s*(.+)',gnu).group(1).strip()
    rss=int(re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)',gnu).group(1))
    swaps=int(re.search(r'Swaps:\s*(\d+)',gnu).group(1)); exit_status=int(re.search(r'Exit status:\s*(\d+)',gnu).group(1))
    assert (elapsed,rss,swaps,exit_status)==('0:00.61',91520,0,0)
    for key in ('cgroup_before','cgroup_after'):
        cg=result[key]
        assert cg['memory.high']=='5368709120' and cg['memory.max']=='7516192768'
        assert cg['memory.swap.max']=='0' and cg['pids.max']=='128'
        assert cg['memory.swap.current']=='0' and cg['memory.swap.peak']=='0'
        assert all(int(v)==0 for k,v in (line.split() for line in cg['memory.events'].splitlines()) if k in ('high','max','oom','oom_kill','oom_group_kill'))
    assert result['cgroup_after']['memory.peak']=='160153600'
    assert result['peak_rss_kib']==rss and result['swap_count']==swaps and result['wall_time']==elapsed
    launch_text=(RUN/'launch-history/54e804310fa3-20261003T050407Z/launch.log').read_text()
    translation_text=(OUT/'translate.log').read_text()
    # Record byte hashes for every physically saved artifact under this one run.
    run_files={str(p.relative_to(OUT)):sha(p.read_bytes()) for p in sorted(OUT.rglob('*')) if p.is_file()}
    launch_dir=RUN/'launch-history/54e804310fa3-20261003T050407Z'
    launch_files={str(p.relative_to(launch_dir)):sha(p.read_bytes()) for p in sorted(launch_dir.rglob('*')) if p.is_file()}
    report={
      'status':'PASS',
      'scope':'Saved-output custody, resource metrics, manifest, external-template/warning inventory, and callback text comparison only. No Lean compilation or source execution claim.',
      'runs':{'translation_run_id':OUT.name,'launch_revision':launch['source_revision'],'projection_source_revision':launch['projection_source_revision'],'input_sha256':result['input_sha256'],'translator_sha256':result['binary_sha256'],'remote_payload_sha256':launch['remote_payload_sha256'],'launcher_exit_status':launched['launcher_exit_status'],'collection_exit_status':collected['exit_status'],'translator_exit_status':result['translator_exit_status'],'gnu_time_exit_status':exit_status,'wall_time':elapsed,'peak_rss_kib':rss,'swap_count':swaps,'cgroup_memory_peak_bytes':int(result['cgroup_after']['memory.peak']),'cgroup_swap_peak_bytes':int(result['cgroup_after']['memory.swap.peak']),'oom_events':0,'caps':launch['caps']},
      'manifest':{'root_fun284_matches':len(root_rows),'root_impl47_matches':len(impl_rows),'fun284_rust_name':root['rust_name'],'fun284_source':root['source'],'fun284_is_opaque':root['is_opaque'],'impl47_trait_id':impl['impl_trait_def_id'],'impl47_trait_name':impl['impl_trait_rust_name'],'functions':len(manifest['functions']),'types':len(manifest['types']),'globals':len(manifest['globals']),'trait_decls':len(manifest['trait_decls']),'trait_impls':len(manifest['trait_impls']),'opaque_function_count':sum(1 for f in manifest['functions'] if f['is_opaque']),'generated_axiom_declaration_lines':axiom_lines},
      'external_templates':{'expected_filenames':['FunsExternal_Template.lean','TypesExternal_Template.lean'],'present':[],'axiom_hole_names':{}},
      'warnings':[],
      'generated_artifacts':expected_files,
      'callback_comparison':{'reference_path':str(R174),'reference_sha256':sha(R174.read_bytes()),'reference_declaration':'R174 rawCallMut','generated_declaration':'Fun284 call_mut','body_token_equal':True,'body_normalizations':['field namespace qualification only: field. vs aspis_core.field.','pretty-printer whitespace only; all other body tokens preserved'],'signature_headers':{'R174_rawCallMut':norm_old_head,'R439_Fun284_call_mut':norm_gen_head},'signature_header_hashes':{'R174_rawCallMut':sha(norm_old_head.encode()),'R439_Fun284_call_mut':sha(norm_gen_head.encode())},'signature_differences_recorded':['declaration identifier rawCallMut vs generated callback name','field module qualification','generated input product type uses explicit grouping parentheses'],'normalized_body_sha256':sha(normalized_generated_body.encode())},
      'preserved_generated_components':['full Fun284 callback body (token-equal to R174 rawCallMut after field namespace normalization)','FunOnce call_once bridge (Fun283)','FnMut and FnOnce generated trait-implementation dictionaries','Types.lean with QM31 and closure pair type plus generated pending-return carrier Type87'],
      'no_compile_boundary':'No Lean target was compiled and no axioms were printed. Aeneas manifest marks all 20 emitted functions non-opaque, and no external-template files or axiom declarations were emitted; this is not a proof of Rust/Aeneas semantic correspondence.',
      'saved_run_files':run_files,'saved_launch_files':launch_files,
      'full_output_log_sha256':{'systemd_launch_log':sha(launch_text.encode()),'translator_stdout_stderr_log':sha(translation_text.encode()),'gnu_time_file':sha(gnu.encode())}
    }
    output=pathlib.Path(__file__).resolve().parent/'audit-report.json'
    output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'status':'PASS','fun284_impl47':True,'callback_normalized_equal':True,'metrics':report['runs'],'report':str(output)},indent=2))
if __name__=='__main__':main()
