#!/usr/bin/env python3
"""Read-only receipt, theorem-audit and endpoint signature checks."""
import hashlib, json, pathlib, re, subprocess
root = pathlib.Path(__file__).resolve().parents[1]
packet = root/'r1p-final'
repo = pathlib.Path(subprocess.check_output(['git','rev-parse','--show-toplevel'],text=True).strip())
records = [json.loads(line) for line in (packet/'history-attempts-9800-9999.jsonl').read_text().splitlines()]
assert all(9800 <= r['attempt'] <= 9999 and r['env']=='J' for r in records)
assert len({r['attempt'] for r in records}) == len(records)
assert len({(r['source_sha256'],r['deps_fingerprint']) for r in records}) == len(records)
assert all(r['swaps']=='0' for r in records)
allowed = {'propext','Classical.choice','Quot.sound'}
final = {}
for r in records:
    if r['exit']==0:
        final[r['module']] = r
pins=[]; audits=[]
for module,r in sorted(final.items()):
    src = root/'lean'/(module+'.lean')
    source = src.read_text()
    assert hashlib.sha256(src.read_bytes()).hexdigest()==r['source_sha256'],module
    found = re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", r['output'], re.S)
    for name, ax in found:
        axioms={v.strip() for v in ax.split(',') if v.strip()}
        assert axioms <= allowed,(module,name,axioms)
        audits.append({'name':name,'axioms':sorted(axioms),'attempt':r['attempt']})
    for theorem in re.findall(r'^theorem (\w+)',source,re.M):
        assert any(a['name'].endswith('.'+theorem) and a['attempt']==r['attempt'] for a in audits),(module,theorem)
    code=re.sub(r'/\-.*?\-/','',source,flags=re.S)
    code=re.sub(r'--[^\n]*','',code)
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|maxHeartbeats|maxRecDepth)\b',code),module
    pins.append({'module':module,'attempt':r['attempt'],'source_sha256':r['source_sha256'],
                 'exit':r['exit'],'wall':r['wall'],'peak_rss_kib':r['peak_rss_kib'],'swaps':r['swaps'],
                 'source_revision':r['source_revision'],'deps_fingerprint':r['deps_fingerprint']})
protected=['PrivacyR1Final.lean','PrivacyR1FinalProtocol.lean','BuilderSource.lean','SourceIdentification.lean']
for name in protected:
    path=root/'lean/R1Z'/name
    if path.exists():
        before=subprocess.check_output(['git','show','d93756b49:'+str(path.relative_to(repo))])
        assert before==path.read_bytes(),name
subprocess.run(['python3',str(packet/'build-history-endpoint.py'),'--check'],check=True)
original=(root/'lean/R1Z/PrivacyR1FinalProtocol.lean').read_text()
new=(root/'lean/R1Z/PrivacyR1FinalProtocolHistory.lean').read_text()
def header(s,name):
    start=s.index('theorem '+name+'\n'); return s[start:s.index(' := by',start)]
a=header(original,'privacy_R1_protocol')
b=header(new,'privacy_R1_protocol_history')
# All original input text preceding the coupling handoffs and the conclusion
# are unchanged, modulo the theorem name.
assert a[a.index('    (seed :'):a.index('    (R_wire_builder_checker')]==b[b.index('    (seed :'):b.index('    (realBad :')]
assert a[a.index('    ZK_FSS'):]==b[b.index('    ZK_FSS'):]
# Gather independent launcher source pins and object hashes/sizes, no binaries.
remote='dombarker@100.108.41.90'
j='/home/dombarker/project-offloads/aspis-joint-20261019'
t='/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence'
commands=[]
for p in pins:
    obj=j+'/objects/'+p['module']+'.olean'
    commands.extend(['cat '+t+'/sha-'+str(p['attempt'])+'.txt','sha256sum '+obj,'stat -c %s '+obj])
lines=subprocess.check_output(['ssh',remote,'set -e\n'+'\n'.join(commands)],text=True).splitlines()
assert len(lines)==len(pins)*3
for k,p in enumerate(pins):
    assert lines[3*k].split()[0]==p['source_sha256']
    p.update(object_sha256=lines[3*k+1].split()[0],object_bytes=int(lines[3*k+2]))
expected_deps={}
for r in final.values():
    for item in r['dependency_objects']:
        digest,path=item.split(maxsplit=1)
        assert path not in expected_deps or expected_deps[path]==digest,('dependency mismatch',path)
        expected_deps[path]=digest
current=subprocess.check_output(['ssh',remote,'sha256sum '+' '.join(sorted(expected_deps))],text=True)
for item in current.splitlines():
    digest,path=item.split(maxsplit=1)
    assert expected_deps[path]==digest,('changed dependency object',path)
report=(packet/'PRIVACY-HISTORY-20261021.md').read_text()
assert b in report,'quoted endpoint does not match source'
assert a[a.index('    (R_wire_builder_checker'):a.index('    ZK_FSS')] in report
result={'base_revision':'d93756b49','audit_revision':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
        'attempt_count':len(records),'unchanged_duplicate_attempts':0,'all_attempt_swaps_zero':True,
        'protected_sources_unchanged':protected,'new_theorem_audit_count':len(audits),
        'final_targets':pins,'axiom_audits':audits,'current_dependency_objects_verified':len(expected_deps),
        'quoted_signatures_match_sources':True,
        'endpoint_scope':'ideal model scan law discharged; real model law retained explicitly; per-history universal bound refuted'}
(packet/'history-final-audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'attempts':len(records),'final_targets':len(pins),'theorem_audits':len(audits),'status':'passed'}))
