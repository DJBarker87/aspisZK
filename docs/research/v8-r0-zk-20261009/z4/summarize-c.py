#!/usr/bin/env python3
"""Audit the Z4c log, including exact replay of Z4b inputs and terminal values."""
import ast, collections, hashlib, json, pathlib, re
here=pathlib.Path(__file__).resolve().parent
root=here.parents[3]
text=(here/'probe-C.log').read_text(); old=(here/'probe-B.log').read_text()
evidence=json.loads((here/'evidence-C.json').read_text())
for file,digest in evidence['source_sha256'].items():
    assert hashlib.sha256((root/file).read_bytes()).hexdigest()==digest,file
source_manifest=json.loads((here/'SOURCE_MANIFEST-C.json').read_text())
assert source_manifest['base_revision']==evidence['base_revision']
for file,digest in source_manifest['sha256'].items():
    assert hashlib.sha256((root/file).read_bytes()).hexdigest()==digest,file
old_ch={int(re.search(r'trial=(\d+)',line)[1]):line for line in old.splitlines() if line.startswith('CHALLENGE ')}
old_ob={(int(re.search(r'trial=(\d+)',line)[1]),int(re.search(r'pair=(\d+)',line)[1])):line.split(' pinned=')[1] for line in old.splitlines() if line.startswith('TERMINAL_OBSTRUCTIONS ')}
replayed=0
for line in text.splitlines():
    if line.startswith('CHALLENGE '):assert line==old_ch[int(re.search(r'trial=(\d+)',line)[1])]
    if line.startswith('Z4B_REPLAY '):
        key=(int(re.search(r'trial=(\d+)',line)[1]),int(re.search(r'pair=(\d+)',line)[1]))
        assert line.split(' pinned=')[1]==old_ob[key],key
        replayed+=1
c1=[];gates=[];results=[]
for line in text.splitlines():
    if line.startswith('C1_C '):
        m=re.fullmatch(r'C1_C trial=(\d+) pattern=(\w+) ranks=(\[.*\]) want_each=112',line)
        assert m,line
        c1.append({'trial':int(m[1]),'pattern':m[2],'ranks':ast.literal_eval(m[3])})
    if line.startswith('GATE_C '):
        label=line.split(' design=')[0][7:];fields=dict(re.findall(r'(\w+)=([^ ]+)',line.split(' design=')[1]))
        design=line.split(' design=')[1].split()[0]
        gates.append({'label':label,'design':design,**{key:int(fields[key]) for key in ['silent_rank','initial_retained_rank','full_conditioned_rank','i_pass','ii_pass','attempted']}})
    if line.startswith('RESULT '):
        head,support=line.split(' quotient_support=');support,pivots=support.split(' excess_pivots=')
        fields=dict(re.findall(r'(image_rank|targets|failures|excess_rank)=(\d+)',head))
        results.append({'label':head[7:].split(' image_rank=')[0],**{k:int(v) for k,v in fields.items()},'quotient_support':ast.literal_eval(support),'excess_pivots':ast.literal_eval(pivots)})
stop=[line for line in text.splitlines() if line.startswith('STOP ')]
review_stop=[]
for gate in gates:
    gate['silent_rank_exact']=gate['silent_rank']==1076
    gate['conditioned_rank_exact']=gate['full_conditioned_rank']==1080
    gate['i_containment']='certified' if gate['i_pass']==gate['attempted'] else 'unresolved_outside_constructed_subspace'
    gate['ii_containment']='certified' if gate['ii_pass']==gate['attempted'] else 'unresolved_outside_constructed_subspace'
    if gate['design']=='libra' and (gate['i_pass']<gate['attempted'] or gate['ii_pass']<gate['attempted']):
        review_stop.append(gate['label'])
aggregate={}
for design in ['libra','columns26']:
    rows=[g for g in gates if g['design']==design and g['label'].startswith('trial=')]
    diagnostic=[r for r in results if r['label'].startswith('trial=') and r['label'].endswith(design+'_derivative_diagnostic')]
    aggregate[design]={'challenges_completed':len(rows),'planned_targets':100,'attempted':sum(g['attempted'] for g in rows),'i_pass':sum(g['i_pass'] for g in rows),'ii_pass':sum(g['ii_pass'] for g in rows),'derivative_diagnostic_pass':sum(r['targets']-r['failures'] for r in diagnostic),'silent_ranks':sorted(set(g['silent_rank'] for g in rows)),'initial_retained_ranks':sorted(set(g['initial_retained_rank'] for g in rows)),'full_conditioned_ranks':sorted(set(g['full_conditioned_rank'] for g in rows))}
    if not stop:
        assert aggregate[design]['challenges_completed']==20
        assert aggregate[design]['i_pass']==aggregate[design]['ii_pass']==100
        assert aggregate[design]['silent_ranks']==[1076]
c1_aggregate={}
for pattern in ['random','consecutive']:
    rows=[row for row in c1 if row['pattern']==pattern]
    assert all(len(row['ranks'])==16 for row in rows)
    c1_aggregate[pattern]={'challenges_checked':len(rows),'column_checks':16*len(rows),'ranks_per_column':[sorted(set(row['ranks'][c] for row in rows)) for c in range(16)]}
    if not stop:
        assert len(rows)==20
        if pattern=='random':assert c1_aggregate[pattern]['ranks_per_column']==[[112]]*16
if not stop:
    assert replayed==100
    assert len([g for g in gates if g['label'].startswith('control=')])==26
    assert 'Z4C_DONE trials=20 i_pass=100 ii_pass=100' in text
    assert all(receipt['exit_status']==0 for receipt in evidence['receipts'])
summary={'base_revision':evidence['base_revision'],'seed':'0x5348f0b9a87835d0','exact_Z4b_replayed_targets':replayed,'compiled_source_hashes_verified':len(evidence['source_sha256']),'decision_source_hashes_verified':len(source_manifest['sha256']),'stop':stop,'review_stop':review_stop,'matrix_scope':'Constructive zero-batched-word lifts. Generic rank 1076 reaches the full silent-image upper bound. Lower degenerate ranks and their excess supports do not establish failure against the entire image. No further arithmetic probe was run after reviewing the degenerate excess.','aggregate':aggregate,'c1_aggregate':c1_aggregate,'c1':c1,'gates':gates,'results':results,'alpha9_half':[line for line in text.splitlines() if line.startswith('ALPHA9_HALF ')]}
(here/'summary-C.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({key:summary[key] for key in ['exact_Z4b_replayed_targets','compiled_source_hashes_verified','stop','review_stop','aggregate']},indent=2))
