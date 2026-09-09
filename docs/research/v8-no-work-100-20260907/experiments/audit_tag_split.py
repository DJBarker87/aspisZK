#!/usr/bin/env python3
"""Compare pinned complete SBF controls; no CU estimates replace measurements."""
import contextlib,hashlib,io,json,re,runpy
from pathlib import Path
ROOT=Path(__file__).resolve().parent.parent
EX=ROOT/'experiments'
with contextlib.redirect_stdout(io.StringIO()):
    prior=runpy.run_path(str(EX/'audit_scatter_performance.py'))
check,summary=prior['check'],prior['summary']
old=prior['maximum']; old_summary=summary(old)
sets={}
for mode in ('split','bounded'):
    name=f'copy-tag-{mode}-max-v1'
    rows={p.stem:check(json.loads(p.read_text())) for p in sorted((ROOT/'evidence/tag-split'/name).glob('*.json'))}
    assert len(rows)==24,(name,len(rows))
    for key,x in rows.items():
        assert x['execution']['txv1_declared_compute_unit_limit']==1200000
        assert x['execution']['outcome']==old[key]['execution']['outcome']
        assert x['execution']['error']==old[key]['execution']['error']
        assert x['artifacts']['token_program']['explicit_pinned_sbf_control']['variant']=='legacy35'
        for role in ('pool','registry'):
            assert x['artifacts'][role]['sha256']==old_summary['artifact_hashes'][role]
    s=summary(rows)
    savings={}
    for shape,vals in s['shapes'].items():
        ov=old_summary['shapes'][shape]
        assert [x['proof_sha256'] for x in vals]==[x['proof_sha256'] for x in ov]
        assert all(x['body']==40282 for x in vals)
        savings[shape]=[a['cu']-b['cu'] for a,b in zip(ov,vals)]
    sets[mode]={'summary':s,'same_proof_saving_over_scatter':savings,
        'improves_every_success':all(n>0 for xs in savings.values() for n in xs),
        'worst_observed':max(x['cu'] for xs in s['shapes'].values() for x in xs)}

supplement={}
for kind,count in (('ordinary',24),('rollback',2)):
    rows={p.stem:check(json.loads(p.read_text())) for p in sorted(
        (ROOT/'evidence/tag-split'/f'copy-tag-bounded-{kind}-v1').glob('*.json'))}
    assert len(rows)==count
    for key,x in rows.items():
        assert x['execution']['txv1_declared_compute_unit_limit']==1200000
        assert x['artifacts']['selected_verifier']['sha256']==sets['bounded']['summary']['artifact_hashes']['selected_verifier']
        if kind=='ordinary':
            assert x['artifacts']['token_program']['explicit_pinned_sbf_control']['variant']=='legacy35'
            assert x['execution']['error']==prior['ordinary'][key]['execution']['error']
            assert x['execution']['outcome']==prior['ordinary'][key]['execution']['outcome']
        else:
            assert x['execution']['selected_verifier_cpi_observed_in_logs']
            assert x['scenario']=='withdrawal-cpi-failure'
    supplement[kind]=summary(rows) if kind=='ordinary' else {'checked_cases':count}

lean=(EX/'copy-tag-split-lean.log').read_text()
sha=hashlib.sha256((EX/'CopyTagSplit.lean').read_bytes()).hexdigest()
assert lean.startswith(sha)
assert 'error:' not in lean and 'sorryAx' not in lean
axioms=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",lean)
assert len(axioms)==10
assert all(set(a.split(', '))<= {'propext','Classical.choice','Quot.sound'} for _,a in axioms)
resources={}
for name in ('copy-tag-split-test','copy-tag-split-sbf-build','copy-tag-bounded-test','copy-tag-bounded-sbf-build'):
    log=(ROOT/'evidence/tag-split'/f'{name}.log').read_text()
    assert '\tExit status: 0' in log
    assert not re.search(r'Stack offset .* exceeded|error:',log)
    wall=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([\d:.]+)',log)[1]
    parts=list(map(float,wall.split(':')))
    seconds=sum(n*60**i for i,n in enumerate(reversed(parts)))
    resources[name]={'exit':0,'wall_seconds':seconds,
        'peak_rss_kib':int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',log)[1]),
        'swaps':int(re.search(r'Swaps: (\d+)',log)[1])}
    assert resources[name]['swaps']==0

out={'schema':'aspis.research.tag-split.v1','base_revision':'4d5f3063412349f5cba9b0b6b7d166d24814eb91',
    'controls':sets,'bounded_supplement':supplement,'body_maximum_bytes':40282,'new_proof_or_transcript_bytes':0,
    'grinding_credit_bits':0,'lean':{'source_sha256':sha,'log':'experiments/copy-tag-split-lean.log',
        'axioms':dict(axioms),'exit':0,'wall_seconds':float(re.search(r'([\d.]+) real',lean)[1]),
        'rss_bytes':int(re.search(r'(\d+)  maximum resident set size',lean)[1]),
        'swaps':int(re.search(r'(\d+)  swaps',lean)[1]),
        'scope':'Exact natural-number congruence and all-prefix ranges. Not translated Rust/compiler equivalence.'},
    'resources':resources,'global_security_certificate':None,'universal_cu_bound':None}
v7=prior['v7']
out['bounded_excess_over_same_pool_v7']={s:max(x['cu'] for x in xs)-v7[s][0]['cu']
    for s,xs in sets['bounded']['summary']['shapes'].items()}
out['margin_to_1200000']=1200000-sets['bounded']['worst_observed']
out['selected_control']='bounded' if sets['bounded']['improves_every_success'] else 'scatter'
print(json.dumps(out,indent=2))
