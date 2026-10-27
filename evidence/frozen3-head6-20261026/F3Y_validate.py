#!/usr/bin/env python3
"""Validate source/receipt/axiom coverage, without launching any build."""
from pathlib import Path
import hashlib,json,re,subprocess
E=Path(__file__).resolve().parent;ROOT=E.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=[];covered={};axioms=[]
for n in range(1,101):
    a=f'F3Y_{n:03}';d=E/a;r=json.loads((d/'receipt.json').read_text())
    assert r['attempt']==a and r['exit_status']==0,a
    assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},a
    assert r['swaps']=='0',a
    assert '-M7000' in r['command'] and len(r['sources'])==1,a
    assert r['kind']=='lean' and r['deps_fingerprint']['selected_objects'],a
    assert all(v['sha256'] and v['bytes'] for v in r['deps_fingerprint']['selected_objects'].values()),a
    log=(d/'stdout.log').read_text()
    assert not re.search(r'\berror(?:\(|:)|sorryAx',log),a
    for s in r['sources']:
        assert sha(d/'sources'/s)==r['source_hashes'][s],a
        assert sha(ROOT/'lean'/s)==r['source_hashes'][s],('current source differs',a,s)
        covered[s]=dict(attempt=a,sha256=r['source_hashes'][s])
    for line in r['print_axioms']:
        if 'depends on axioms:' in line:
            names=set(line.split('[',1)[1].split(']',1)[0].split(', '))
            assert names<={'propext','Classical.choice','Quot.sound'},(a,line)
        axioms.append(dict(attempt=a,line=line))
    rows.append(r)
# Every theorem in every new proof module has a successful printed audit.
theorems=[]
for p in sorted((ROOT/'lean').glob('F3Y_*.lean')):
    s=p.read_text();assert p.name in covered,p.name
    assert not re.search(r'\b(sorry|admit|native_decide)\b|^\s*axiom\s|set_option\s+(maxRecDepth|maxHeartbeats)',s,re.M),p.name
    ns=re.search(r'^namespace ([\w.]+)',s,re.M)
    for m in re.finditer(r'^theorem (\w+)',s,re.M):
        fullname=ns[1]+'.'+m[1]
        lines=[a for a in axioms if "'"+fullname+"'" in a['line']]
        assert lines,('missing axiom audit',fullname)
        theorems.append(dict(theorem=fullname,source=p.name,sha256=sha(p),audits=lines))
# Stage1 was a byte-identical rebuild of committed delivered F3X.
stage1=json.loads((E/'F3Y_STAGE1.json').read_text())
for m,h in stage1['sources'].items():assert sha(ROOT/'lean'/(m+'.lean'))==h
(E/'F3Y_attempts.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in rows))
(E/'F3Y_source-manifest.json').write_text(json.dumps(covered,indent=2)+'\n')
(E/'F3Y_theorems.json').write_text(json.dumps(theorems,indent=2)+'\n')
(E/'F3Y_axioms.json').write_text(json.dumps(axioms,indent=2)+'\n')
log=(E/'F3Y_070/stdout.log').read_text()
for name,label in [('Rc5_Top.deployed','BEFORE'),('F3Y_Headline.deployed','AFTER'),('F3Y_Nonvacuity.composed','NONVACUITY')]:
    begin=log.index('@AspisR1.'+name+' :');end=log.find('\n@AspisR1.',begin+1)
    if end<0:end=log.find("\n'AspisR1.",begin)
    if end<0:end=len(log)
    (E/('F3Y_'+label+'.lean.txt')).write_text(log[begin:end]+'\n')
result=dict(lean_attempts=100,passes=100,failures=0,kani_runs=0,budget_exhausted=True,
    wall_seconds=sum(r['wall_seconds'] for r in rows),peak_rss_kib=max(int(r['peak_rss_kib']) for r in rows),swaps=0,
    unique_checked_modules=len(covered),new_top_theorems=len(theorems),axiom_audit_lines=len(axioms),
    stage1_delivered_modules=32,stage2_refinement_modules=16,stage3_composition_modules=3,stage4_inventory_modules=49,
    current_source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
    final_statement_sha256=sha(E/'F3Y_AFTER.lean.txt'),before_statement_sha256=sha(E/'F3Y_BEFORE.lean.txt'),
    headline_receipt='F3Y_050/receipt.json',nonvacuity_receipt='F3Y_051/receipt.json',
    scope='Focused coherent delivered F3X and new F3Y closure over unchanged pinned SInt2/native/candidate cache. No package replay or frozen-release rebuild.',
    remaining='L159;13 source-global finish laws plus12 native-local finish laws, accepted observations, P2Prime/FirstEntry, approved game/runtime/trust/source-to-ELF boundaries. Target not yet established unconditionally.')
(E/'F3Y_FINAL.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
