#!/usr/bin/env python3
"""Check focused receipts, current sources/dependencies, scope and signature claims.
No Lean replay; inherited cache coherence remains a separate release obligation.
"""
from pathlib import Path
import hashlib,json,re,subprocess,difflib
root=Path(__file__).resolve().parents[5]
base=root/'docs/research/100bit-spend-path-20261013'
ev=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
revision='71b7f0db3309a85bb3f7331ecca45b2466ef8a6a'
manifest=json.loads((ev/'manifest.json').read_text())
last={}
for r in manifest['attempts']:
    d=ev/(r['module']+'-'+str(r['attempt']))
    assert sha(d/'source.lean')==r['source_sha256']
    assert json.loads((d/'receipt.json').read_text())==r
    assert (d/'lean.log').exists() and (d/'time.log').exists()
    assert all(k in r for k in ['argv','source_revision','deps_fingerprint','exit',
        'wall_seconds','peak_rss_bytes','swaps','axioms','errors'])
    last[r['module']]=r
rows=[]
for module,r in sorted(last.items()):
    assert r['exit']==0,(module,'last attempt failed')
    src=base/'lean'/(module+'.lean')
    assert sha(src)==r['source_sha256'],(module,'stale source')
    for dep in r['direct_imports']:
        assert sha(Path(dep['path']))==dep['sha256'],(module,'stale dependency',dep)
    assert r['swaps']==0
    assert r['peak_rss_bytes']<4400*1024*1024
    for line in r['axioms']:
        ax=re.search(r'\[([^]]*)\]',line)
        if ax: assert set(x.strip() for x in ax[1].split(',') if x.strip()) <= {'propext','Classical.choice','Quot.sound'},line
    text=src.read_text()
    names=re.findall(r'^(?:private )?theorem\s+(\w+)',text,re.M)
    for name in names:
        assert f'#print axioms {name}' in text,(module,name,'missing audit command')
        assert any('.'+name+"'" in a for a in r['axioms']),(module,name,'missing audit result')
    assert not re.search(r'\b(sorry|sorryAx|native_decide|axiom)\b|set_option\s+(maxRecDepth|maxHeartbeats)',
        re.sub(r'/-.*?-/', '',text,flags=re.S))
    # `admit` is a defined guard function; disallow the tactic, not that identifier.
    assert not re.search(r'^\s*(?:by\s+)?admit\s*$',text,re.M)
    obj=Path(r['argv'][r['argv'].index('-o')+1])
    rows.append({'module':module,'attempt':r['attempt'],'exit':0,
        'wall_seconds':r['wall_seconds'],'peak_rss_bytes':r['peak_rss_bytes'],
        'swaps':r['swaps'],'source_sha256':r['source_sha256'],'source_revision':r['source_revision'],
        'axiom_reports':len(r['axioms']),'object_sha256':sha(obj),'object_bytes':obj.stat().st_size})
# No previously existing file in the repository was changed.
changes=subprocess.check_output(['git','diff','--name-status',revision],cwd=root,text=True).splitlines()
assert all(line.startswith('A\t') for line in changes),changes
for path in subprocess.check_output(['git','ls-files','--others','--exclude-standard'],cwd=root,text=True).splitlines():
    if '/lean/' in path: assert Path(path).name.startswith('OraclePort'),path
for line in changes:
    path=line.split('\t')[-1]
    if '/lean/' in path: assert Path(path).name.startswith('OraclePort'),path
# Existing endpoints remain exactly unchanged, with an empty deletion diff.
sigs=[]
for name in ['R1FinalSoundnessBinPerQueryR19','R1FinalSoundnessHeadline']:
    path=base/'lean'/(name+'.lean')
    before=subprocess.check_output(['git','show',revision+':'+str(path.relative_to(root))],cwd=root)
    assert before==path.read_bytes()
    sigs.append({'module':name,'base_sha256':hashlib.sha256(before).hexdigest(),'current_sha256':sha(path),'diff':''})
(ev/'existing-headline-signature.diff').write_text('')
# Only the NEW kernel budget binder is deleted after specialization.
before=(ev/'kernel-specialized-before.lean.txt').read_text()
after=(ev/'kernel-specialized-after.lean.txt').read_text()
binder='    (hbudget : Budget (OraclePortMultiKernel.decision cs duplicates frames))\n'
assert before.replace(binder,'')==after and before.count(binder)==1
assert (ev/'kernel-budget-deletion-only.diff').read_text()==''.join(difflib.unified_diff(
    before.splitlines(True),after.splitlines(True),fromfile='kernel-specialized-before',tofile='kernel-specialized-after'))
(ev/'signature-audit.json').write_text(json.dumps({'existing_endpoint_deletions':0,
    'existing_endpoints':sigs,'new_kernel_only_deleted_binder':binder.strip(),
    'not_claimed':['R16/R13/R14/R15/R3 discharge at frozen dV','complete frozen parser','Rust equality','M10 adequacy on shifted domain']},indent=2)+'\n')
result={'status':'pass','scope':'focused cache-based proof evidence; incomplete frozen dV port',
    'modules':rows,'attempt_count':len(manifest['attempts']),
    'failed_attempts':sum(r['exit']!=0 for r in manifest['attempts']),
    'axiom_reports':sum(r['axiom_reports'] for r in rows),
    'peak_final_rss_bytes':max(r['peak_rss_bytes'] for r in rows),
    'swaps':sum(r['swaps'] for r in manifest['attempts'])}
(ev/'audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='modules'},indent=2))
