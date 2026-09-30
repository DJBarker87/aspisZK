#!/usr/bin/env python3
"""Audit fixed source tests, kernel certificates and their exact limited scope."""
import argparse,hashlib,json,re,subprocess,sys
from pathlib import Path
from generate_r120_certificate import make
p=argparse.ArgumentParser();p.add_argument('--record',action='store_true');a=p.parse_args()
root=Path(__file__).resolve().parent.parent;repo=root.parents[2]
e=root/'evidence/r120-augmented-section'
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
def j(f):return json.loads(f.read_text())
def blob(h):
    f=e/'blobs'/h;assert sha(f)==h;return f
def metric(f):
    s=f.read_text();t=re.findall(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([\d:.]+)',s)[-1]
    return {'exit':int(re.findall(r'Exit status: (\d+)',s)[-1]),'swaps':int(re.findall(r'Swaps: (\d+)',s)[-1]),
      'wall_s':round(sum(float(x)*60**i for i,x in enumerate(reversed(t.split(':')))),2),
      'peak_rss_kib':int(re.findall(r'Maximum resident set size \(kbytes\): (\d+)',s)[-1])}
def caps(f):
    c=j(f);assert [c[k]for k in ['memory.high','memory.max','memory.swap.max','pids.max']]==[str(5*2**30),str(7*2**30),'0','128']
subprocess.run([sys.executable,str(root/'tools/check_r117_evidence.py')],stdout=subprocess.DEVNULL,check=True)
subprocess.run([sys.executable,str(root/'tools/freeze_r120_manifest.py'),'--check'],stdout=subprocess.DEVNULL,check=True)
pm=j(e/'control/r18-stage.json')
assert pm==j(root/'evidence/r117-native-engine/r117-primal/r18-stage.json')
assert sha(e/'control/r18-stage.json')=='26755a4250ec6075005e840565040414b694deb97fb1830fc95aff2692d34fb6'
collection=j(e/'collection.json')
assert not any(collection[k]for k in ['private_fixtures_collected','compiled_objects_collected','wallet_keys_collected','verifier_changed'])
source_reports={};source_arts={}
for name,record in collection['sources'].items():
    d=e/name;m=j(d/'r18-stage.json');s=j(d/'sources.json');arts=j(d/'artifacts.json');source_arts[name]=arts
    number=int(name[1:4]);assert len(m['files'])==record['pins']
    assert s=={n:h for n,h in m['files'].items()if pm['files'].get(n)!=h} and len(s)==3
    assert all(n in m['files']for n in pm['files'])
    for h in [*s.values(),*arts.values()]:blob(h)
    cfg=m[f'r{number}_boundary'];assert cfg['control_manifest_sha256']==sha(e/'control/r18-stage.json')
    assert not any(cfg[k]for k in ['verifier_changed','profile_changed','accepted_prefix','universal_coverage','full_security'])
    assert cfg['primal_helper_exact_prefix']
    commands=j(blob(arts['commands.json']));assert len(commands)==2 and all(r['exit']==0 for r in commands)
    assert '--release' in commands[0]['command'] and '--jobs' in commands[0]['command']
    caps(blob(arts['resources.json']))
    logs={n:metric(blob(h))for n,h in arts.items()if n.endswith('.log')}
    assert all(r['exit']==r['swaps']==0 for r in logs.values())
    meta=j(blob(arts['metadata.json']));assert meta['source_manifest_sha256']==sha(d/'r18-stage.json')
    assert meta['overflow_checks'] and not meta['full_security']
    result=j(blob(arts['results/summary.json']))
    assert result['actual_two_swap_source'] and not any(result[k]for k in ['accepted_prefix','universal_coverage','full_security'])
    if number==118:
        assert [(c['selected_rank'],c['root_independent_precondition'])for c in result['cases']]==[(1,True),(13,False),(10,True)]
    else:
        c=result['cases'][0]
        assert c['selected_rank']==c['full_rank']==13 and c['normalization_checks']==1700 and c['low_column_checks']==1173
        assert c['extra_root_one'] and c['root_independent_precondition'] and c['point_low_nonzero']==[0,88,0] and c['channel_low_nonzero']==[88,88]
    source_reports[name]={'result':result,'metrics':logs,'source_manifest_sha256':sha(d/'r18-stage.json')}
src=source_arts['r120-source']
for name in ['source-weights.json','high_code_support_pivot_check.json']:
    assert sha(e/'source-results'/name)==src['results/'+name]
weights=j(e/'source-results/source-weights.json');cert=j(e/'source-results/high_code_support_pivot_check.json')
assert cert['determinant']==1190787698 and cert['constant_low_map'] and 'low_zero' not in cert
old=j(blob(source_arts['r119-source']['results/high_code_support_pivot_check.json']))
assert old['low_zero'] and old['matrix']==cert['matrix'] and old['inverse']==cert['inverse']
generated=make(weights,cert)
for name,s in generated.items():assert (root/'lean/AspisV8R19'/name).read_text()==s
plan=j(root/'tools/r120-release-manifest.json');assert len(plan['targets'])==42
formal=j(e/'formal.json');reports={};release=None
failed={
 'aspis-r119-augmented-20260930-a':'AugmentedQuerySection.log',
 'aspis-r120-quotient-20260930-a':'AugmentedQuotient.log',
 'aspis-r120-bridge-20260930-a':'TwoSwapQueryTransport.log',
 'aspis-r120-bridge-20260930-b':'AugmentedMaskTransport.log'}
for name,rec in formal.items():
    arts=rec['artifacts']
    for h in arts.values():blob(h)
    caps(blob(arts['resources.json']))
    logs={};audits={}
    for n,h in arts.items():
        if not n.endswith('.log'):continue
        f=blob(h);m=metric(f);s=f.read_text();logs[n]=m
        assert m['swaps']==0 and m['peak_rss_kib']<7*2**20
        assert m['exit']==(1 if failed.get(name)==n else 0),(name,n,m)
        declarations=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",s,re.S)
        audits[n]={d:[x.strip()for x in axioms.split(',')if x.strip()]for d,axioms in declarations}
        if m['exit']==0:
            assert 'sorryAx' not in s
            assert all(set(xs)<={'propext','Classical.choice','Quot.sound'} for xs in audits[n].values())
    records=j(blob(arts['metadata.json']))
    current=[r for r in records if r.get('command') and str(Path(r['command'][r['command'].index('-o')+1]).parent.parent.parent)==rec['stage']]
    # Match by the exact output prefix, including nested module directories.
    current=[r for r in records if '/'+name+'/lib/' in ' '.join(r.get('command',[]))]
    assert len(current)==len(logs)
    for r in current:
        log=Path(r['target_name']).name+'.log';assert r['exit']==logs[log]['exit']
        assert r['base_revision']==plan['base_revision'] and r['toolchain']==plan['toolchain']
        assert 'lake' in r['command'][0] and r['command'][1:3]==['env','lean'] and '-M4500' in r['command']
    reports[name]={'targets':current,'metrics':logs,'axioms':audits}
    if name=='aspis-r120-release-20260930-a':
        assert [r['target_name']for r in current]==[r['target']for r in plan['targets']]
        assert all(r['exit']==0 for r in current)
        for r,pin in zip(current,plan['targets'],strict=True):
            assert r['source_sha256']==pin['sha256'] and sha(root/'lean'/(r['target_name']+'.lean'))==pin['sha256']
            assert len(audits[Path(r['target_name']).name+'.log'])==pin['axioms_audits']
        release=reports[name]
assert release is not None
summary={'status':'PASS_SCOPED','base_revision':plan['base_revision'],'source_tests':source_reports,
 'formal':reports,'compiled_release_targets':42,'release_axioms_audits':83,
 'release_wall_sum_s':round(sum(m['wall_s']for m in release['metrics'].values()),2),
 'release_max_leaf_rss_kib':max(m['peak_rss_kib']for m in release['metrics'].values()),
 'release_swaps':0,'old_source_witness_rank':1,'new_fixed_matrix_rank':13,
 'R119_inherited_low_zero_label_replaced_by_constant_low_map':True,
 'universal_roots_fixed_model_proved':True,'arbitrary_challenge_source_polynomial_bound':False,
 'actual_source_universal_joint_coverage':False,'full_privacy':False,'full_soundness':False,
 'verifier_changed':False,'new_SBF_runs':0,'unchanged_CU':[999790,999532],
 'first_remaining_proposition':'Bind the augmented section to the complete two-swap source weight map at arbitrary challenges; prove its fixed-query determinant nonzero with a rechecked degree bound, then justify the exceptional-event law in the actual adaptive shared-oracle experiment. This is still only one G-residual gate, not full C1/H1/G joint coverage.'}
paths=[root/'tools'/n for n in ['r118_source_boundary.rs','run_r118_source.py','r119_source_program.py','run_r119_source.py','run_r119_lean.py','r120_source_program.py','run_r120_source.py','generate_r120_certificate.py','freeze_r120_manifest.py','r120-release-manifest.json','run_r120_release.py','collect_r120_evidence.py','check_r120_evidence.py']]
paths+=[root/'lean'/(r['target']+'.lean')for r in plan['targets']]
paths+=[root/'evidence/r117-native-engine/MANIFEST.json']
pins={str(f.relative_to(repo)):sha(f)for f in sorted(paths)}
if a.record:
    (e/'receipt.json').write_text(json.dumps(summary,indent=2,sort_keys=True)+'\n')
    (e/'SOURCE_PINS.json').write_text(json.dumps(pins,indent=2)+'\n')
    (e/'MANIFEST.json').write_text(json.dumps({str(f.relative_to(e)):sha(f)for f in sorted(e.rglob('*'))if f.is_file()and f.name!='MANIFEST.json'},indent=2)+'\n')
assert j(e/'receipt.json')==summary and j(e/'SOURCE_PINS.json')==pins
manifest=j(e/'MANIFEST.json');assert set(manifest)=={str(f.relative_to(e))for f in e.rglob('*')if f.is_file()and f.name!='MANIFEST.json'}
for n,h in manifest.items():assert sha(e/n)==h,n
print(json.dumps({k:summary[k]for k in ['status','compiled_release_targets','release_axioms_audits','release_wall_sum_s','release_max_leaf_rss_kib','universal_roots_fixed_model_proved','actual_source_universal_joint_coverage','full_privacy','full_soundness']}))
