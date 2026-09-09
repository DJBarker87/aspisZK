#!/usr/bin/env python3
"""Audit two rejected, exact gamma-head controls against the retained winner."""
import contextlib,hashlib,io,json,re,runpy,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parent.parent; EX=ROOT/'experiments'; EV=ROOT/'evidence'
REV='e6373fdc297308657f4ea49bbc67b57a47939d22'
with contextlib.redirect_stdout(io.StringIO()):
    prior=runpy.run_path(str(EX/'audit_chord_norm.py'))
check,summary=prior['check'],prior['summary']; base=prior['maximum']; bs=summary(base)
def sha(x):return hashlib.sha256(x).hexdigest()
def blob(name):return subprocess.check_output(['git','show',REV+':docs/research/v8-no-work-100-20260907/experiments/'+name],cwd=ROOT)
def patched(name,patch):
    text=blob(name).decode(); old=[];new=[];active=False
    def replace(text,old,new):
        old=''.join(old);new=''.join(new);assert old and text.count(old)==1
        return text.replace(old,new,1)
    for line in (EX/patch).read_text().splitlines(keepends=True):
        if line.startswith('@@'):
            if active:text=replace(text,old,new)
            old=[];new=[];active=True
        elif active:
            if line[0] in ' -':old.append(line[1:])
            if line[0] in ' +':new.append(line[1:])
    assert active
    return sha(replace(text,old,new).encode())
callback_sha=patched('relation_callback.rs','gamma-one-callback.patch')
variants={};resources={}
for mode,regression in (('gamma-one',1022),('gamma-one-split',647)):
    ev=EV/mode
    rows={p.stem:check(json.loads(p.read_text())) for p in sorted((ev/f'{mode}-max-v1').glob('*.json'))}
    assert len(rows)==24
    raw=rows['withdrawal-255-2-success']
    for key,x in rows.items():
        assert x['execution']['txv1_declared_compute_unit_limit']==1200000
        assert x['fixture']['proof_sha256']==base[key]['fixture']['proof_sha256']
        assert x['artifacts']['selected_verifier']==raw['artifacts']['selected_verifier']
        for role in ('pool','registry','token_program'):assert x['artifacts'][role]==base[key]['artifacts'][role]
        for field in ('outcome','error'):assert x['execution'][field]==base[key]['execution'][field]
    ms=summary(rows)
    delta={s:[a['cu']-b['cu'] for a,b in zip(bs['shapes'][s],xs)] for s,xs in ms['shapes'].items()}
    assert all(x['body']==40282 for xs in ms['shapes'].values() for x in xs)
    assert all(d==-regression for ds in delta.values() for d in ds)
    qs=patched('query_arithmetic.rs',f'{mode}-query.patch')
    measured=(ev/'measured-sources.txt').read_text()
    assert qs in measured and callback_sha in measured
    for job in ('test','sbf-build'):
        path=ev/f'{mode}-{job}-v1.log';log=path.read_text()
        assert '\tExit status: 0' in log and not re.search(r'Stack offset .* exceeded|error:',log)
        if job=='test':
            assert qs in log and '1 passed; 0 failed' in log
            assert 'noncanonical_positions=152 short_inputs=2' in log and 'generic_fallback=true' in log
        parts=list(map(float,re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([\d:.]+)',log)[1].split(':')))
        resources[f'{mode}-{job}']={'exit':0,'wall_seconds':sum(x*60**i for i,x in enumerate(reversed(parts))),
            'rss_kib':int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',log)[1]),
            'swaps':int(re.search(r'Swaps: (\d+)',log)[1]),'log':str(path.relative_to(ROOT))}
        assert resources[f'{mode}-{job}']['swaps']==0
    stack=json.loads((ev/'stack.json').read_text())
    assert stack['max_direct_frame_offset']<=4096 and not stack['unused_warning_function_emitted']
    variants[mode]={'maximum':ms,'same_proof_savings_cu':delta,'selected':False,
        'source_sha256':{'query_arithmetic.rs':qs,'relation_callback.rs':callback_sha},
        'verifier':raw['artifacts']['selected_verifier'],'stack_audit':stack,
        'elf_delta_bytes':raw['artifacts']['selected_verifier']['bytes']-base['withdrawal-255-2-success']['artifacts']['selected_verifier']['bytes'],
        'worst_observed_cu':max(x['cu'] for xs in ms['shapes'].values() for x in xs),
        'ordinary_matrix_run':False,'rollback_matrix_run':False}
lean=(EX/'gamma-one-split-lean.log').read_text(); failed=(EX/'gamma-one-lean.log').read_text()
assert sha((EX/'GammaOne.lean').read_bytes()) in lean and 'error:' not in lean and 'sorryAx' not in lean
axs=dict(re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",lean))
axs.update({n:'' for n in re.findall(r"'([^']+)' does not depend on any axioms",lean)})
assert len(axs)==7 and all(set(filter(None,a.split(', ')))<={'propext','Classical.choice','Quot.sound'} for a in axs.values())
oleans=re.findall(r'([a-f0-9]{64})\s+[^\n]+\.olean',lean);assert len(oleans)==2
if (EX/'GammaOne.olean').exists():assert sha((EX/'GammaOne.olean').read_bytes())==oleans[-1]
assert 'unexpected token' in failed
restored={name:sha(blob(name)) for name in ('query_arithmetic.rs','relation_callback.rs')}
# Pin the restored selected blobs; later source changes must not be silently
# confused with the measured rejected controls.
out={'schema':'aspis.research.gamma-one.v1','base_revision':REV,'variants':variants,'resources':resources,
    'selected':'chord-norm','selected_unchanged_evidence':'chord-norm-results.json',
    'selected_worst_observed_cu':prior['out']['worst_observed_cu'],
    'selected_margin_to_1200000':prior['out']['margin_to_1200000'],
    'selected_verifier':base['withdrawal-255-2-success']['artifacts']['selected_verifier'],
    'selected_source_restoration':restored,'excess_over_same_pool_v7':prior['out']['excess_over_same_pool_v7'],
    'lean':{'source_sha256':sha((EX/'GammaOne.lean').read_bytes()),'olean_sha256':oleans[-1],'axioms':axs,
        'exit':0,'wall_seconds':float(re.search(r'([\d.]+) real',lean)[1]),
        'rss_bytes':int(re.search(r'(\d+)  maximum resident set size',lean)[1]),'swaps':int(re.search(r'(\d+)  swaps',lean)[1])},
    'failed_preflight':{'exit':1,'log':'experiments/gamma-one-lean.log','reason':'prefix is a reserved Lean token; renamed the variable to part.',
        'retained_claimed_proof':False,'wall_seconds':float(re.search(r'([\d.]+) real',failed)[1]),
        'rss_bytes':int(re.search(r'(\d+)  maximum resident set size',failed)[1]),'swaps':int(re.search(r'(\d+)  swaps',failed)[1])},
    'operation_model':{'old_c1_base_products':26*4*4*22,'fast_c1_base_products':25*4*4*22,
        'omitted_base_products':4*4*22,'unchanged_partial_reductions':7*4*4*22,
        'head_array_comparisons_per_prepared_table':1,'split_source_dispatches_per_proof':22,
        'compiler_branch_count_measured':False,'extra_heap_bytes':0},
    'body_maximum':697*16+52+24+22*621+2*296*26,'new_proof_or_transcript_bytes':0,
    'grinding_credit_bits':0,'global_security_certificate':None,'universal_cu_bound':None}
print(json.dumps(out,indent=2))
