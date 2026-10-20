#!/usr/bin/env python3
"""Read-only receipt and additive-scope audit; does not rerun Lean."""
import pathlib, json, re, hashlib, subprocess, difflib
HERE=pathlib.Path(__file__).resolve().parent
ROOT=HERE.parents[4]
TREE=ROOT/'docs/research/100bit-spend-path-20261013'
BASE='e014ff517'
MODULES=['D0ScheduleAdmission','D0InstanceAdmission','D0CanonicalInstance','D0CanonicalSource','D0TypedChecks','D0ErasedWordObstruction','D0OpeningRecoveryObstruction','D0ChecksComposition']
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
receipts=[]; seen=set()
for path in sorted(HERE.glob('*/receipt.json')):
    r=json.loads(path.read_text()); receipts.append(r)
    assert sha(path.parent/'source.lean.txt')==r['source_sha256'], path
    assert all(k in r for k in ['argv','source_revision','deps_fingerprint','exit','wall_seconds','peak_rss_bytes','swaps','axioms','errors'])
    assert r['peak_rss_bytes'] is not None and r['swaps'] is not None
    assert hashlib.sha256(json.dumps(r['direct_imports'],sort_keys=True).encode()).hexdigest()==r['deps_fingerprint']
    key=(r['module'],r['source_sha256'],r['deps_fingerprint'],r['lean_path'])
    assert key not in seen, ('unchanged attempt',path); seen.add(key)
    assert r['argv'][1:4]==['-j1','-M4400','-DElab.async=false']
    assert '/tmp/codex-cx-d0-decision-20261021-objects/' in r['argv'][r['argv'].index('-o')+1]
final=[]; count=0
for module in MODULES:
    source=TREE/'lean'/(module+'.lean')
    text=source.read_text()
    assert not re.search(r'\b(sorry|admit|native_decide)\b|^\s*axiom\b|set_option\s+(maxRecDepth|maxHeartbeats)',text,re.M), module
    rs=[r for r in receipts if r['module']==module and r['exit']==0 and r['source_sha256']==sha(source)]
    assert len(rs)==1, (module,'missing/ambiguous final receipt')
    r=rs[0]
    assert not r['errors'], r
    audits={re.search(r"'([^']+)'",line).group(1):line for line in r['axioms']}
    for name in re.findall(r'^theorem\s+(\w+)',text,re.M):
        assert re.search(r'^#print axioms '+name+r'$',text,re.M), (module,name)
        line=audits['AspisR1.'+module+'.'+name]
        if 'depends on axioms:' in line:
            axioms=set(re.findall(r'\b(?:propext|Classical\.choice|Quot\.sound|sorryAx|[\w]+Ax)\b',line.split('depends on axioms:')[1]))
            tokens={x.strip() for x in line.split('[',1)[1].split(']',1)[0].split(',') if x.strip()}
            assert tokens <= {'propext','Classical.choice','Quot.sound'}, line
        count+=1
    for imp in r['direct_imports']:
        assert sha(pathlib.Path(imp['path']))==imp['sha256'], (module,'dependency changed',imp)
    obj=pathlib.Path(r['argv'][r['argv'].index('-o')+1])
    final.append({'module':module,'attempt':r['attempt'],'exit':r['exit'],'wall_seconds':r['wall_seconds'],'peak_rss_bytes':r['peak_rss_bytes'],'swaps':r['swaps'],'source_revision':r['source_revision'],'source_sha256':r['source_sha256'],'object_sha256':sha(obj),'object_bytes':obj.stat().st_size,'axioms':r['axioms']})
# The current endpoint is preserved, rather than manufacturing a premise deletion.
endpoint=TREE/'lean/R1FinalSoundnessBinPerQueryR19.lean'
relative=str(endpoint.relative_to(ROOT))
before=subprocess.check_output(['git','show',BASE+':'+relative],cwd=ROOT,text=True)
after=endpoint.read_text()
def signature(s):
    start=s.index('theorem final_soundness')
    return s[start:s.index(' := by',start)]+'\n'
a,b=signature(before),signature(after)
(HERE/'signature-before.lean.txt').write_text(a)
(HERE/'signature-after.lean.txt').write_text(b)
diff=''.join(difflib.unified_diff(a.splitlines(True),b.splitlines(True),fromfile='R19-before',tofile='R19-after'))
assert not diff
(HERE/'signature.diff').write_text(diff)
changed=subprocess.check_output(['git','diff','--name-status',BASE,'--'],cwd=ROOT,text=True)
for line in changed.splitlines():
    status,path=line.split('\t',1)
    if '/lean/' in path: assert status=='A' and pathlib.Path(path).stem in MODULES, line
    assert '/lean-candidates/' not in path and 'M10' not in pathlib.Path(path).name, line
report={'schema':'d0-decision-focused-audit-v1','base':BASE,'endpoint_created':False,'endpoint_preserved':'R1FinalSoundnessBinPerQueryR19.final_soundness','premises_removed':[],'signature_diff_empty':True,'attempt_count':len(receipts),'successful_module_count':len(final),'standard_axiom_audit_count':count,'max_final_rss_bytes':max(r['peak_rss_bytes'] for r in final),'total_swaps':sum(r['swaps'] for r in receipts),'results':final}
(HERE/'audit.json').write_text(json.dumps(report,indent=2)+'\n')
(HERE/'manifest.json').write_text(json.dumps({'schema':'focused-extractor-proof-packet-v1','attempts':receipts},indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k!='results'},indent=2))
