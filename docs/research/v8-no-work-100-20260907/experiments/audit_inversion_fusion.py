#!/usr/bin/env python3
"""Audit two measured fusion layouts against the retained circle-norm build."""
import contextlib,hashlib,io,json,re,runpy,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parent.parent;EX=ROOT/'experiments'
REV='09a6dd7aa188b31dd96c898e9b3f5ae296514a70'
with contextlib.redirect_stdout(io.StringIO()):
    prior=runpy.run_path(str(EX/'audit_circle_norm.py'))
check,summary=prior['check'],prior['summary'];base=prior['maximum'];bs=summary(base)
def sha(data):return hashlib.sha256(data).hexdigest()
def patched(name,patchname):
    text=subprocess.check_output(['git','show',REV+':docs/research/v8-no-work-100-20260907/experiments/'+name],cwd=ROOT).decode()
    old=[];new=[];active=False
    def replace(text,old,new):
        old=''.join(old);new=''.join(new);assert old and text.count(old)==1
        return text.replace(old,new,1)
    for line in (EX/patchname).read_text().splitlines(keepends=True):
        if line.startswith('@@'):
            if active:text=replace(text,old,new)
            old=[];new=[];active=True
        elif active:
            if line[0] in ' -':old.append(line[1:])
            if line[0] in ' +':new.append(line[1:])
    assert active
    return sha(replace(text,old,new).encode())
def resource(path):
    log=path.read_text()
    assert '\tExit status: 0' in log and not re.search(r'Stack offset .* exceeded|error:',log)
    parts=list(map(float,re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([\d:.]+)',log)[1].split(':')))
    row={'exit':0,'wall_seconds':sum(x*60**i for i,x in enumerate(reversed(parts))),
        'rss_kib':int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',log)[1]),
        'swaps':int(re.search(r'Swaps: (\d+)',log)[1]),'log':str(path.relative_to(ROOT))}
    assert row['swaps']==0
    return row
def evidence(mode,folder,n):
    rows={p.stem:check(json.loads(p.read_text())) for p in sorted((ROOT/'evidence'/mode/folder).glob('*.json'))}
    assert len(rows)==n
    assert all(x['execution']['txv1_declared_compute_unit_limit']==1200000 for x in rows.values())
    return rows
def compare(rows,old,artifact):
    for key,x in rows.items():
        assert x['fixture']['proof_sha256']==old[key]['fixture']['proof_sha256']
        assert x['artifacts']['selected_verifier']==artifact
        for role in ('pool','registry','token_program'):assert x['artifacts'][role]==old[key]['artifacts'][role]
        for field in ('outcome','error'):assert x['execution'][field]==old[key]['execution'][field]
controls={}
for mode,source in [('joined-inverse','joined_inverse_concat.rs'),('split-inverse','joined_inverse.rs')]:
    maximum=evidence(mode,mode+'-max-v1',24);ms=summary(maximum)
    artifact=maximum['withdrawal-255-2-success']['artifacts']['selected_verifier']
    compare(maximum,base,artifact)
    delta={s:[b['cu']-a['cu'] for a,b in zip(bs['shapes'][s],xs)] for s,xs in ms['shapes'].items()}
    assert all(x['body']==40282 for xs in ms['shapes'].values() for x in xs)
    selected=mode=='split-inverse'
    assert all((d<0 if selected else d>0) for ds in delta.values() for d in ds)
    src={'relation_callback.rs':patched('relation_callback.rs',mode+'-callback.patch'),
         'circle_norm.rs':patched('circle_norm.rs',mode+'-kernel.patch'),
         'joined_inverse.rs':sha(subprocess.check_output(['git','show', '992288fd577f647c810a506fc83b4811fb90f0e6:docs/research/v8-no-work-100-20260907/experiments/joined_inverse.rs'],cwd=ROOT)) if selected else sha((EX/source).read_bytes())}
    ev=ROOT/'evidence'/mode;test=(ev/(mode+'-test-v1.log')).read_text()
    assert all(h in test for h in src.values()) and '1 passed; 0 failed' in test
    assert 'chord_profiles=1024 general_batches=512 zero_positions=132' in test
    stack=json.loads((ev/'stack.json').read_text())
    assert stack['max_direct_frame_offset']<=4096 and not stack['unused_warning_function_emitted']
    row={'maximum':ms,'same_proof_delta_cu':delta,'selected':selected,'artifact':artifact,
         'source_sha256':src,'stack_audit':stack,
         'resources':{job:resource(ev/(mode+'-'+job+'-v1.log')) for job in ('test','sbf-build')},
         'ordinary':None,'rollback_cases':None}
    if selected:
        ordinary=evidence(mode,mode+'-ordinary-v1',24);rollback=evidence(mode,mode+'-rollback-v1',2)
        compare(ordinary,prior['ordinary'],artifact);compare(rollback,prior['rollback'],artifact)
        assert all(x['execution']['selected_verifier_cpi_observed_in_logs'] for x in rollback.values())
        row['ordinary']=summary(ordinary);row['rollback_cases']=2
    row['worst_observed_cu']=max(x['cu'] for xs in ms['shapes'].values() for x in xs)
    row['elf_delta_bytes']=artifact['bytes']-base['withdrawal-255-2-success']['artifacts']['selected_verifier']['bytes']
    controls[mode]=row
lean=(EX/'joined-inverse-final-lean.log').read_text();source=(EX/'JoinedInverse.lean').read_bytes()
assert sha(source) in lean and 'error:' not in lean and 'sorryAx' not in lean
assert not re.search(rb'\b(sorry|axiom)\b',source)
axs=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",lean)
assert len(axs)==11 and all(set(a.split(', '))<={'propext','Classical.choice','Quot.sound'} for _,a in axs)
olean=re.findall(r'([a-f0-9]{64})\s+[^\n]+/JoinedInverse\.olean',lean)[-1]
if (EX/'JoinedInverse.olean').exists():assert sha((EX/'JoinedInverse.olean').read_bytes())==olean
selected=controls['split-inverse']
out={'schema':'aspis.research.inversion-fusion.v1','base_revision':REV,'controls':controls,
     'selected':'split-inverse','worst_observed_cu':selected['worst_observed_cu'],
     'margin_to_1200000':1200000-selected['worst_observed_cu'],
     'excess_over_same_pool_v7':{s:max(x['cu'] for x in xs)-max(x['cu'] for x in bs['shapes'][s])+prior['out']['excess_over_same_pool_v7'][s] for s,xs in selected['maximum']['shapes'].items()},
     'operation_model':{'old_inversions':2,'new_inversions':1,'inv_chain_m31_products':38,
        'old_batch_products':3*(88-1)+3*(44-1),'new_batch_products':3*(132-1),
        'net_m31_products_saved':35,'joined_requested_payload_delta_bytes':176,
        'split_requested_payload_delta_bytes':0,'actual_peak_allocator_delta_bytes':None},
     'lean':{'source_sha256':sha(source),'olean_sha256':olean,'axioms':dict(axs),'exit':0,
        'wall_seconds':float(re.search(r'([\d.]+) real',lean)[1]),
        'rss_bytes':int(re.search(r'(\d+)  maximum resident set size',lean)[1]),
        'swaps':int(re.search(r'(\d+)  swaps',lean)[1])},
     'body_maximum':697*16+52+24+22*621+2*296*26,'new_proof_or_transcript_bytes':0,
     'grinding_credit_bits':0,'universal_cu_bound':None,'global_security_certificate':None,
     'prover_time_delta_seconds':None,
     'refinement_status':'Kernel-checked prefix/backward field model, exact zero guards and split seeds; source mapping and differential tests, not translated Rust/LLVM/SBF.'}
assert out['lean']['swaps']==0
print(json.dumps(out,indent=2))
