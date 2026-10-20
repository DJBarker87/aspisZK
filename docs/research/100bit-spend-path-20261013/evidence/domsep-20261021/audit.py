#!/usr/bin/env python3
"""Audit focused receipts, source restrictions and unchanged endpoint signatures."""
import pathlib, subprocess, hashlib, json, re
root=pathlib.Path(__file__).resolve().parents[5]
base=root/'docs/research/100bit-spend-path-20261013'
ev=pathlib.Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
manifest=json.loads((ev/'manifest.json').read_text())
for r in manifest['attempts']:
    d=ev/(r['module']+'-'+r['attempt'])
    assert sha((d/'source.lean').read_bytes())==r['source_sha256']
    assert r['peak_rss_bytes'] is not None and r['swaps'] is not None
    assert r['argv'][1:4]==['-j1','-M4400','-DElab.async=false']
    assert sha(json.dumps(r['direct_imports'],sort_keys=True).encode())==r['deps_fingerprint']
    for dep in r['direct_imports']:
        assert dep['sha256'] and sha(pathlib.Path(dep['path']).read_bytes())==dep['sha256']
mods=sorted((base/'lean').glob('OracleDecisionDomSep*.lean'))
for p in mods:
    matching=[r for r in manifest['attempts'] if r['module']==p.stem and r['source_sha256']==sha(p.read_bytes()) and r['exit']==0]
    assert matching, 'No green receipt for '+p.name
    audits=matching[-1]['axioms']
    names=re.findall(r'^theorem\s+(\w+)',p.read_text(),re.M)
    printed=re.findall(r'^#print axioms (\w+)',p.read_text(),re.M)
    assert sorted(names)==sorted(printed)
    assert len(audits)==len(names)
    for line in audits:
        if 'depends on axioms:' in line:
            assert set(re.split(r',\s*',re.search(r'\[([^]]*)\]',line)[1].strip())) <= {'propext','Classical.choice','Quot.sound'},line
    assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b|set_option\s+(maxRecDepth|maxHeartbeats)',p.read_text())
base_rev='0559b538f'
changed=subprocess.check_output(['git','diff','--name-only',base_rev],cwd=root,text=True).splitlines()
for p in changed:
    if p.endswith('.lean') and '/lean/' in p:
        exists=subprocess.run(['git','cat-file','-e',base_rev+':'+p],cwd=root,stderr=subprocess.DEVNULL).returncode==0
        assert not exists,'Existing Lean module changed: '+p
        assert pathlib.Path(p).name.startswith('OracleDecisionDomSep')
endpoints=[]
for p in sorted((base/'lean').glob('R1FinalSoundness*.lean')):
    rel=str(p.relative_to(root))
    frozen=subprocess.check_output(['git','show',base_rev+':'+rel],cwd=root)
    assert frozen==p.read_bytes()
    endpoints.append({'path':rel,'base_sha256':sha(frozen),'current_sha256':sha(p.read_bytes()),'signature_diff':''})
(ev/'signature-audit.json').write_text(json.dumps({'base':base_rev,'premise_removal_claimed':False,'endpoints':endpoints},indent=2)+'\n')
result={'status':'pass','new_modules':[p.stem for p in mods],'attempts':len(manifest['attempts']),'successful_final_theorem_audits':sum(len([r for r in manifest['attempts'] if r['module']==p.stem and r['source_sha256']==sha(p.read_bytes()) and r['exit']==0][-1]['axioms']) for p in mods),'unchanged_endpoints':len(endpoints),'full_lean_manifest_replay':False,'reason':'Focused prerequisite modules only; no generated certificate or endpoint changed.'}
(ev/'audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
