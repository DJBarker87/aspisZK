#!/usr/bin/env python3
"""Focused source, generator, provenance and accepted-receipt audit."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2]
P=R/'docs/research/100bit-spend-path-20261013'
E=P/'evidence/ckpt-bytes5-20261022'
BASE='942f5e3a5'
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
for generator in ['generate.py','generate_trace.py']:
    subprocess.run(['python3','-B',str(R/'tools/ckpt-bytes5-20261022'/generator),'--check'],check=True)
subprocess.run(['python3','-B',str(R/'tools/ckpt-bytes5-20261022/source_check.py')],check=True)
manifest=json.loads((E/'manifest.json').read_text())
current={a['module']:a for a in manifest['attempts'] if a['final_current']}
modules=sorted((P/'lean').glob('CheckpointBytes5*.lean'))
assert set(current)=={p.stem for p in modules},(set(current),[p.stem for p in modules])
assert len(current['CheckpointBytes5Freeze']['axioms'])==36
theorems=0
for p in modules:
    a=current[p.stem]
    assert a['exit']==0 and a['source_unchanged'] and a['axioms_accepted']
    assert sha(p)==a['source_sha256'],p
    assert a['swaps']==0
    assert not re.search(r'\b(?:sorry|admit|native_decide)\b|^\s*axiom\b|set_option\s+(?:maxHeartbeats|maxRecDepth)',p.read_text(),re.M),p
    names=re.findall(r'^(?:private )?theorem (\w+)',p.read_text(),re.M)
    for name in names:
        assert any(report.split("'",2)[1].endswith('.'+name) for report in a['axioms']), (p,name)
    theorems+=len(names)
    for dep in a['owned_transitive_dependencies']:
        assert sha(R/dep['source'])==dep['source_sha256'],dep['module']
    for dep in a['direct_imports']:
        assert sha(dep['path'])==dep['sha256'],dep['module']
    for key in ['argv','source_revision','wall_seconds','peak_rss_bytes','swaps','axioms','deps_fingerprint']:
        assert key in a
    for suffix in ['receipt.json','command.json','source.lean.txt','lean.log','time.log']:
        assert (E/(p.stem+'-'+str(a['attempt']))/suffix).exists()
changed=subprocess.check_output(['git','diff','--name-only',BASE],cwd=R,text=True).splitlines()
untracked=subprocess.check_output(['git','ls-files','--others','--exclude-standard'],cwd=R,text=True).splitlines()
changed=sorted(set(changed+untracked))
assert not any(p.startswith(('crates/','programs/')) or '/lean-candidates/' in p for p in changed)
assert not any(p.endswith('.lean') and '/CheckpointBytes5' not in p for p in changed)
assert not any(p.endswith(('.olean','.tar','.tar.gz','.elf')) for p in changed)
assert all(p.stat().st_size<=5_000_000 for p in E.rglob('*.json'))
old=P/'evidence/ckpt-bytes4-20261022'
reuse=json.loads((old/'reuse.json').read_text())
assert reuse['exit']==0 and not reuse['gates_reexecuted'] and not reuse['lean_axiom_adoption']
assert sha(R/'crates/aspis-r1-cost-probe/src/verifier.rs')==reuse['source_verifier_sha256']
assert sha(P/'evidence/ckpt-bytes3-20261022/audit-result.json')==reuse['previous_audit_result_sha256']
reused={'previous_audit_result_sha256':sha(old/'audit-result.json'),
        'previous_manifest_sha256':sha(old/'manifest.json'),
        'previous_reuse_sha256':sha(old/'reuse.json'),
        'prior_native_gates':reuse,'gates_reexecuted':False,'lean_axiom_adoption':False}
(E/'reuse.json').write_text(json.dumps(reused,indent=2)+'\n')
result={'schema':'ckpt-bytes5-focused-audit-v1',
 'source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),
 'modules':len(modules),'new_theorems':theorems,'current_swaps':sum(a['swaps'] for a in current.values()),
 'current_peak_rss_bytes':max(a['peak_rss_bytes'] for a in current.values()),
 'retained_resume_source_reconstruction':True,'writer_content_effects':True,
 'six_ordered_saved_byte_reads':True,'successful_saved_fields_consumed':True,
 'success_conditioned_checkpoint_content_stage_join':True,
 'reached_decision_checkpoint_replacement':True,
 'remaining_named_refinements':['S2S10CallerBinding','S1S7S8StateProvenance'],
 'frozen_rust_source_program_interpretation_closed':False,
 'whole_verifier_accepted_run_join_inhabited':False,
 'coherent_release_replay':False,'elf_rebuild_trigger':False,
 'host_env_j_attempts_used':[],
 'next_consumer':'Discharge actual S2/S10 caller/ROM carriers and S1/S7/S8 canonical saved-ten input provenance at the retained P6 boundary; install decision_success_join in the complete raw and annotation-pass frozen2 AcceptedRunJoin.'}
(E/'audit-result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
