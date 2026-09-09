#!/usr/bin/env python3
"""Pin profile and rejected/winning controls to identical complete proofs."""
import contextlib,hashlib,io,json,re,runpy,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parent.parent; EX=ROOT/'experiments'; EV=ROOT/'evidence'
REV='7ccf84a3b8c66c30a9db96fb9cb305849b65106b'
with contextlib.redirect_stdout(io.StringIO()):
    prior=runpy.run_path(str(EX/'audit_leaf_record.py'))
check,summary=prior['check'],prior['summary']
base=prior['maximum']; bs=summary(base)
def sha(data): return hashlib.sha256(data).hexdigest()
def load(mode,suffix,count):
    rows={p.stem:check(json.loads(p.read_text())) for p in sorted((EV/mode/f'{mode}-{suffix}-v1').glob('*.json'))}
    assert len(rows)==count
    assert all(x['execution']['txv1_declared_compute_unit_limit']==1200000 for x in rows.values())
    return rows
def compare(rows,old):
    for key,x in rows.items():
        assert x['fixture']['proof_sha256']==old[key]['fixture']['proof_sha256']
        for role in ('pool','registry','token_program'): assert x['artifacts'][role]==old[key]['artifacts'][role]
        for field in ('outcome','error'): assert x['execution'][field]==old[key]['execution'][field]

# Replay only literal text hunks IN MEMORY against the pinned source. This
# preserves the exact source of each measured build as later research evolves.
original=subprocess.run(['git','show',REV+':docs/research/v8-no-work-100-20260907/experiments/query_arithmetic.rs'],cwd=ROOT,check=True,capture_output=True).stdout.decode()
def source_hash(patch):
    text=original; old=[];new=[];active=False
    def replace(text,old,new):
        old=''.join(old);new=''.join(new)
        assert old and text.count(old)==1,patch
        return text.replace(old,new,1)
    for line in (EX/patch).read_text().splitlines(keepends=True):
        if line.startswith('@@'):
            if active: text=replace(text,old,new)
            old=[];new=[];active=True
        elif active:
            if line[0] in ' -': old.append(line[1:])
            if line[0] in ' +': new.append(line[1:])
    assert active
    return sha(replace(text,old,new).encode())

variants={}; sets={}; resources={}
for mode in ('gamma-fused','decode-blocks'):
    rows=load(mode,'max',24);sets[mode]=rows;compare(rows,base)
    ms=summary(rows);delta={}
    for shape,xs in ms['shapes'].items():
        assert all(x['body']==40282 for x in xs)
        delta[shape]=[a['cu']-b['cu'] for a,b in zip(bs['shapes'][shape],xs)]
    raw=rows['withdrawal-255-2-success']; stack=json.loads((EV/mode/'stack.json').read_text())
    assert stack['max_direct_frame_offset']<=4096 and not stack['unused_warning_function_emitted']
    sh=source_hash(f'{mode}-control.patch')
    for job in ('test','sbf-build'):
        path=EV/mode/f'{mode}-{job}-v1.log';log=path.read_text()
        assert '\tExit status: 0' in log and not re.search(r'Stack offset .* exceeded|error:',log)
        if job=='test':
            assert '1 passed; 0 failed' in log and sh in log
            assert 'noncanonical_positions=152 short_inputs=2' in log
        parts=list(map(float,re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([\d:.]+)',log)[1].split(':')))
        resources[f'{mode}-{job}']={'exit':0,'wall_seconds':sum(x*60**i for i,x in enumerate(reversed(parts))),
            'rss_kib':int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',log)[1]),
            'swaps':int(re.search(r'Swaps: (\d+)',log)[1]),'log':str(path.relative_to(ROOT))}
        assert resources[f'{mode}-{job}']['swaps']==0
    variants[mode]={'maximum':ms,'same_proof_savings_cu':delta,'source_sha256':sh,'stack_audit':stack,
        'verifier':raw['artifacts']['selected_verifier'],
        'elf_delta_bytes':raw['artifacts']['selected_verifier']['bytes']-base['withdrawal-255-2-success']['artifacts']['selected_verifier']['bytes'],
        'worst_observed_cu':max(x['cu'] for xs in ms['shapes'].values() for x in xs),
        'selected':mode=='decode-blocks'}
assert all(v<0 for xs in variants['gamma-fused']['same_proof_savings_cu'].values() for v in xs)
assert all(v==1320 for xs in variants['decode-blocks']['same_proof_savings_cu'].values() for v in xs)
ordinary=load('decode-blocks','ordinary',24);rollback=load('decode-blocks','rollback',2)
compare(ordinary,prior['ordinary']);compare(rollback,prior['rollback'])
for x in [*ordinary.values(),*rollback.values()]:
    assert x['artifacts']['selected_verifier']['sha256']==variants['decode-blocks']['verifier']['sha256']
for x in rollback.values(): assert x['execution']['selected_verifier_cpi_observed_in_logs']

profile=check(json.loads((EV/'decode-profile/decode-profile-v1/withdrawal-255-2.json').read_text()))
assert profile['fixture']['proof_sha256']==base['withdrawal-255-2-success']['fixture']['proof_sha256']
for role in ('pool','registry','token_program'): assert profile['artifacts'][role]==base['withdrawal-255-2-success']['artifacts'][role]
assert profile['execution']['txv1_declared_compute_unit_limit']==1200000
logs=profile['execution']['logs']
marks=[(a.split('Program log: ')[-1],int(re.search(r'(\d+) units remaining',b)[1])) for a,b in zip(logs,logs[1:])
    if a.startswith('Program log: v8:') and re.search(r'(\d+) units remaining',b)]
intervals={}
for a,b in zip(marks,marks[1:]): intervals.setdefault(b[0],[]).append(a[1]-b[1])
for label in ('v8:decode-c1','v8:decode-c2','v8:gamma-dots'): assert len(intervals[label])==22
profile_source=source_hash('decode-profile.patch')
assert profile_source in (EV/'decode-profile/decode-profile-v1/artifact-hashes.txt').read_text()
plog=(EV/'decode-profile/decode-profile-build-v1.log').read_text()
assert '\tExit status: 0' in plog and not re.search(r'Stack offset .* exceeded|error:',plog)
parts=list(map(float,re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([\d:.]+)',plog)[1].split(':')))
resources['profile-build']={'exit':0,'wall_seconds':sum(x*60**i for i,x in enumerate(reversed(parts))),
    'rss_kib':int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',plog)[1]),
    'swaps':int(re.search(r'Swaps: (\d+)',plog)[1]),'log':'evidence/decode-profile/decode-profile-build-v1.log'}
assert resources['profile-build']['swaps']==0
lean=(EX/'decode-blocks-final-lean.log').read_text();failed=(EX/'decode-blocks-lean.log').read_text()
assert sha((EX/'DecodeBlocks.lean').read_bytes()) in lean
assert 'error:' not in lean and 'sorryAx' not in lean and 'error:' in failed
axs=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",lean)
assert len(axs)==6 and all(set(a.split(', '))<={'propext','Quot.sound','Classical.choice'} for _,a in axs)
oleans=re.findall(r'([a-f0-9]{64})\s+[^\n]+\.olean',lean)
assert len(oleans)==2
if (EX/'DecodeBlocks.olean').exists(): assert sha((EX/'DecodeBlocks.olean').read_bytes())==oleans[-1]
out={'schema':'aspis.research.decode-controls.v1','base_revision':REV,'variants':variants,'resources':resources,
    'selected':'decode-blocks','ordinary':summary(ordinary),'rollback_cases':len(rollback),
    'profile':{'complete_cu':profile['execution']['compute_units'],'source_sha256':profile_source,
        'verifier':profile['artifacts']['selected_verifier'],'intervals':{k:{'count':len(v),'sum_cu':sum(v),'min_cu':min(v),'max_cu':max(v)} for k,v in intervals.items()},
        'scope':'Instrumented complete execution; intervals include checkpoint/codegen effects, not standalone CU predictions.'},
    'lean':{'source_sha256':sha((EX/'DecodeBlocks.lean').read_bytes()),'olean_sha256':oleans[-1],'axioms':dict(axs),
        'exit':0,'wall_seconds':float(re.search(r'([\d.]+) real',lean)[1]),
        'rss_bytes':int(re.search(r'(\d+)  maximum resident set size',lean)[1]),'swaps':int(re.search(r'(\d+)  swaps',lean)[1])},
    'failed_preflight':{'exit':1,'log':'experiments/decode-blocks-lean.log',
        'reason':'Explicit membership simplification needed the empty-list case; fixed locally without changing Rust or memory cap.',
        'retained_claimed_proof':False,'wall_seconds':float(re.search(r'([\d.]+) real',failed)[1]),
        'rss_bytes':int(re.search(r'(\d+)  maximum resident set size',failed)[1]),'swaps':int(re.search(r'(\d+)  swaps',failed)[1])},
    'body_maximum':697*16+52+24+22*621+2*296*26,'new_proof_or_transcript_bytes':0,'extra_heap_bytes':0,
    'grinding_credit_bits':0,'global_security_certificate':None,'universal_cu_bound':None}
out['worst_observed_cu']=variants['decode-blocks']['worst_observed_cu']
out['margin_to_1200000']=1200000-out['worst_observed_cu']
out['excess_over_same_pool_v7']={s:prior['out']['excess_over_same_pool_v7'][s]-1320 for s in bs['shapes']}
print(json.dumps(out,indent=2))
