#!/usr/bin/env python3
"""Focused receipt integrity and selected-body association; no semantic proof."""
from pathlib import Path
import hashlib,json,re,resource,subprocess,time
R=Path(__file__).resolve().parents[2];E=R/'evidence/port24sbfmap-20261024';D=R/'docs/research/100bit-spend-path-20261013/evidence/s10-repin3-20261023'
t=time.monotonic();x=json.loads((E/'selected-implementation.json').read_text());m=json.loads((D/'build-manifest.json').read_text());inputs=x['inputs']
checks=[]
def check(name,condition):
    assert condition,name
    checks.append(name)
expected={o['path']:o for b in m['builds'] for o in b['outputs'] if not o['path'].endswith('-keypair.json')}
matched=[];unlisted=[]
for p,row in inputs.items():
    if p in expected:
        check('retained-output:'+p,all(row[k]==expected[p][k] for k in ['bytes','sha256']));matched.append(p)
    else:unlisted.append(p)
check('source revision',x['source_revision']==m['source_revision']=='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387')
check('collector pin',x['inspection_receipt']['script_sha256']==hashlib.sha256((R/'tools/port24sbfmap-20261024/Port24SBFMAP_collect.py').read_bytes()).hexdigest())
pins={b['comparison']['mode']:b['comparison']['sha256'] for b in m['builds']}
rows={}
for mode,b in x['builds'].items():
    check(mode+' deployed pin',b['elf']['deployed']['sha256']==pins[mode])
    check(mode+' text equality',b['elf']['text_equal'])
    shim=next(s for s in b['selected_elf_symbols'] if s['name'].endswith('12___rust_alloc'))
    check(mode+' alloc instruction inventory',len(shim['instructions'])==34 and shim['bytes']==272)
    check(mode+' alloc no call opcode',all(i['opcode'] not in [0x85,0x8d] for i in shim['instructions']))
    fs=[(p,f) for p in b['ir'] for f in p['functions']]
    alloc=[f for p,f in fs if '___rustc12___rust_alloc(' in f['header']]
    check(mode+' unique emitted alloc',len(alloc)==1)
    end=12884901888+(32768 if mode=='pool' else 262144)
    check(mode+' concrete arena',str(end) in alloc[0]['text'] and '12884901896' in alloc[0]['text'])
    mir=[f for p in b['mir'] for f in p['functions'] if f['header'].startswith('fn heap::filled(')]
    check(mode+' concrete Global MIR',len(mir)==1 and 'alloc: const alloc::alloc::Global' in mir[0]['text'] and 'len: const 0_usize' in mir[0]['text'])
    associations=[]
    for p,f in fs:
        check(mode+' excerpt hash '+str(f['start']),hashlib.sha256(f['text'].encode()).hexdigest()==f['sha256'])
        sym=re.search(r'@(?:"([^"]+)"|([^ (]+))\(',f['header']);name=(sym[1] or sym[2]) if sym else None
        final=[s for s in b['selected_elf_symbols'] if s['name']==name]
        associations.append({'ir_path':p['path'],'start':f['start'],'end':f['end'],'ir_sha256':f['sha256'],'signature':f['header'],'symbol':name,'selected_final_symbols':final,'scope':'exact symbol spelling association only; correctness of lowering retained under P7, inline map absent'})
    rows[mode]={'arena_start':12884901888,'arena_bytes':end-12884901888,'cursor_metadata_bytes':8,'alloc_symbol':shim,'associations':associations}
check('same verifier alloc machine bytes',rows['default']['alloc_symbol']['machine_sha256']==rows['devnet']['alloc_symbol']['machine_sha256'])
check('Pool alloc differs',rows['default']['alloc_symbol']['machine_sha256']!=rows['pool']['alloc_symbol']['machine_sha256'])
source_manifest=json.loads((D/'source-inputs.json').read_text())
check('source manifest pin',inputs[x['root']+'/source-inputs.json']['sha256']==hashlib.sha256((D/'source-inputs.json').read_bytes()).hexdigest())
for s in x['sources']:
    source=R/s['pin']['path'];check('current source '+s['pin']['path'],hashlib.sha256(source.read_bytes()).hexdigest()==s['pin']['sha256'])
# Every unlisted input is either a source selected by the frozen manifest, the
# manifest itself, or the retained root-program diagnostic command.
allowed={x['root']+'/src/'+s['path'] for s in source_manifest['files']}
allowed.add(x['root']+'/source-inputs.json')
allowed.update(p for b in x['builds'].values() for p in b['diagnostic_commands'])
check('no unclassified inputs',all(p in allowed for p in unlisted))
(E/'binding-map.json').write_text(json.dumps({'schema':'Port24SBFMAP-selected-associations-v1','builds':rows,'limitations':['No sysroot source or archive content pin is supplied by the current source manifest.','Generic emitted bodies absent from the selected final symbols are not promoted to deployed out-of-line instances.','Symbol names, raw instruction inventory and LLVM attributes are not primitive/native proofs.']},indent=2)+'\n')
u=resource.getrusage(resource.RUSAGE_SELF)
pinfiles=[E/'selected-implementation.json',E/'inspection-receipt.json',D/'build-manifest.json',D/'source-inputs.json',R/'tools/port24sbfmap-20261024/Port24SBFMAP_collect.py',R/'tools/port24sbfmap-20261024/Port24SBFMAP_run.py',Path(__file__)]
receipt={'command':['python3','tools/port24sbfmap-20261024/Port24SBFMAP_verify.py'],'exit_status':0,'wall_seconds':time.monotonic()-t,'peak_rss_bytes_macos':u.ru_maxrss,'swaps':u.ru_nswap,'source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),'print_axioms':'N/A: Python integrity checks, no Lean proof','checks':checks,'retained_outputs_rehashed':len(matched),'other_classified_inputs':unlisted,'dependencies':{str(p.relative_to(R)):{'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size} for p in pinfiles}}
(E/'validation.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({'exit_status':0,'checks':len(checks),'retained_outputs_rehashed':len(matched),'new_formal_proofs':0}))
