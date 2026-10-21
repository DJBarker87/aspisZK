#!/usr/bin/env python3
"""Read-only focused freeze audit. Never launches Lean or rebuilds caches."""
from pathlib import Path
import hashlib,json,re,subprocess,difflib
ROOT=Path(__file__).resolve().parents[2]
BASE=ROOT/'docs/research/100bit-spend-path-20261013'
E=BASE/'evidence/oracle-port-draft-20261021'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
manifest=json.loads((E/'OraclePortContinuation7Manifest.json').read_text())
allowed={'propext','Classical.choice','Quot.sound'}
latest={};seen=set();final=[]
for a in manifest['attempts']:
    out=E/f"{a['module']}-{a['attempt']}"
    assert json.loads((out/'receipt.json').read_text())==a
    assert sha(out/'source.lean.txt')==a['source_sha256']
    assert a['argv'][1:4]==['-j1','-M4400','-DElab.async=false']
    assert a['lean_path'].split(':')[0]=='/tmp/codex-cx-oracle-port-c7-20261021-objects'
    for key in ['source_revision','deps_fingerprint','exit','wall_seconds','peak_rss_bytes','swaps','axioms','errors']:
        assert key in a,(a['module'],key)
    assert a['swaps']==0
    assert a['peak_rss_bytes']<8*1024**3
    fp=hashlib.sha256(json.dumps(a['direct_imports'],sort_keys=True).encode()).hexdigest()
    assert fp==a['deps_fingerprint']
    key=(a['module'],a['source_sha256'],fp)
    assert key not in seen,key
    seen.add(key)
    log=(out/'lean.log').read_text()
    reports=re.findall(r"'[^']+' (?:depends on axioms: \[[\s\S]*?\]|does not depend on any axioms)",log)
    assert reports==a['axioms']
    assert a['source_revision']==subprocess.check_output(['git','rev-parse',a['source_revision']],cwd=ROOT,text=True).strip()
    if a['exit']==0:
        assert not a['errors']
        for report in reports:
            names=set(re.findall(r'[A-Za-z][A-Za-z0-9_.]*',report.split('depends on axioms: [')[-1])) if 'depends on axioms: [' in report else set()
            assert names<=allowed,(a['module'],names)
    latest[a['module']]=a
for module,a in sorted(latest.items()):
    assert a['exit']==0,module
    src=BASE/'lean'/f'{module}.lean'
    assert sha(src)==a['source_sha256']
    assert a['final_current']
    assert sha(f'/tmp/codex-cx-oracle-port-c7-20261021-objects/{module}.olean')==a['object_sha256']
    for imp in a['direct_imports']:
        assert sha(imp['path'])==imp['sha256'],(module,imp)
    text=src.read_text()
    assert not re.search(r'\b(sorry|native_decide|maxRecDepth|maxHeartbeats)\b|^\s*(axiom|admit)\s',text,re.M)
    for name in re.findall(r'^theorem\s+(\w+)',text,re.M):
        assert f'#print axioms {name}' in text,(module,name)
        assert any(f'.{name}\'' in report for report in a['axioms']),(module,name)
    final.append(a)
changed=subprocess.check_output(['git','diff','--name-status','b81ae0928','--',str(BASE/'lean')],cwd=ROOT,text=True)
for line in changed.splitlines():
    status,path=line.split('\t')
    assert status=='A' and Path(path).name.startswith('OraclePort'),line
pin=json.loads((E/'OraclePortC7M10ImportPin.json').read_text())
assert pin['receipt']['exit']==0
obj=next(i for i in latest['OraclePortHeadlineDVC7']['direct_imports'] if i['module']=='ClosedAllocationLedgerM10')
assert obj['sha256']==pin['receipt']['object_sha256']
for source in pin['sources']:
    data=subprocess.check_output(['git','show',pin['revision']+':'+str(BASE.relative_to(ROOT)/'lean'/source['path'])],cwd=ROOT)
    assert hashlib.sha256(data).hexdigest()==source['sha256']
assert pin['receipt']['source_sha256']==next(x['sha256'] for x in pin['sources'] if x['path']=='ClosedAllocationLedgerM10.lean')
expected_path='/tmp/codex-cx-oracle-port-c7-20261021-objects:'+pin['command']['lean_path']+':'+json.loads((E/'OraclePortStoredAcceptanceC6-1/command.json').read_text())['lean_path']
assert latest['OraclePortHeadlineDVC7']['lean_path']==expected_path
freeze=json.loads((E/'OraclePortC7FrozenSources.json').read_text())
assert len(freeze['modules'])==len(latest)
for frozen in freeze['modules']:
    assert sha(ROOT/frozen['path'])==frozen['sha256']
assert latest[freeze['root']]['attempt']==1 and latest[freeze['root']]['exit']==0
comparison=json.loads((E/'OraclePortC7Comparison.json').read_text())
v3=subprocess.check_output(['git','show',comparison['comparison_revision']+':'+str(BASE.relative_to(ROOT)/'lean/R1FinalSoundnessHeadlineV3.lean')],cwd=ROOT)
assert hashlib.sha256(v3).hexdigest()==comparison['v3_sha256']
assert v3==(E/'OraclePortC6-v3-before.lean.txt').read_bytes()
# Deletion-only artifacts are compared against the actual checked signatures.
s=(BASE/'lean/OraclePortPremiseDeletionC7.lean').read_text()
def signature(name):
    a=s.index('theorem '+name+'\n')+len('theorem '+name+'\n')
    return s[a:s.index(' :=',a)]+'\n'
names=['h_R16_instance','h_R13','h_R14_backend','h_R15_writer','h_R3_semantic','h_Rwire_tag']
for n,name in enumerate(names):
    before=signature(f'model_stage{n}');after=signature(f'model_stage{n+1}')
    d=''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='before',tofile='after'))
    assert d==(E/f'OraclePortC7-delete-{name}.diff').read_text()
    assert not any(l.startswith('+') and not l.startswith('+++') for l in d.splitlines())
    assert (E/f'OraclePortC7-{name}-verbatim.lean.txt').read_text() in before
before=signature('model_stage6');after=signature('model_without_source')
assert ''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='before',tofile='after'))==(E/'OraclePortC7-delete-source.diff').read_text()
s=(BASE/'lean/OraclePortHeadlineDVC7.lean').read_text()
def headline(name):
    a=s.index('theorem '+name+'\n');b=s.index(' :=',a)
    return (s[a:b].replace('theorem '+name,'theorem final_soundness',1)+'\n').replace(') :\n',')\n    :\n')
before=headline('final_soundness_of_clean');after=headline('final_soundness')
assert before==(E/'OraclePortC7-headline-before.lean.txt').read_text()
assert after==(E/'OraclePortC7-headline-after.lean.txt').read_text()
assert before.replace('    (h_model : CleanAcceptedModel D (projected D P) (bad Q))\n','')==after
assert ''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='before',tofile='after'))==(E/'OraclePortC7-delete-model.diff').read_text()
summary={'schema':'oracle-port-c7-focused-freeze-v1','status':'PASS','modules':len(final),'attempts':len(manifest['attempts']),'successful_attempts':sum(a['exit']==0 for a in manifest['attempts']),'failed_attempts':sum(a['exit']!=0 for a in manifest['attempts']),'final_axiom_reports':sum(len(a['axioms']) for a in final),'peak_rss_bytes':max(a['peak_rss_bytes'] for a in manifest['attempts']),'all_zero_swap':True,'source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),'v3_comparison_revision':comparison['comparison_revision'],'existing_lean_edits':0,'M10_source_or_object_rebuilds':0,'execution_join_proved':False,'runtime_binding_proved':False,'modules_final':[{'module':a['module'],'sha256':a['source_sha256'],'axioms':a['axioms']} for a in final]}
(E/'OraclePortC7Audit.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:v for k,v in summary.items() if k!='modules_final'},indent=2))
