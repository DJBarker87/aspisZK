from pathlib import Path
import subprocess,json,time,re,os
E=Path(__file__).resolve().parent;os.chdir(E)
L='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake'
base=[L,'env','lean','-j1','-M7000','-DElab.async=false'];steps=[]
def save(n,v):Path(n).write_text(json.dumps(v,indent=2)+'\n')
def run(name,args,expect=0):
 start=time.monotonic()
 with open(name+'.log','w') as log:r=subprocess.run(['/usr/bin/time','-v','-o',name+'-time.log','timeout','120',*base,*args],stdout=log,stderr=subprocess.STDOUT)
 t=Path(name+'-time.log').read_text();log=Path(name+'.log').read_text()
 row=dict(target=name,command=base+args,exit_status=r.returncode,expected_exit=expect,wall_seconds=time.monotonic()-start,print_axioms=re.findall(r"'[^']+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)",log))
 for key,label in [('peak_rss_kib','Maximum resident set size'),('swaps','Swaps')]:row[key]=next(l.split(':',1)[1].strip() for l in t.splitlines() if label in l)
 steps.append(row);save('PREFLIGHT-STEPS.json',steps);print(name,r.returncode,flush=True)
 assert r.returncode==expect,(name,log)
 assert 'declaration uses \'sorry\'' not in log and 'PANIC' not in log,log
 return log
# Smallest required generic module, then fixture dependencies, then the changed driver.
for name in ['NEP_WALKER','NEP_Planted','NEP_Mutations','PV_D595_Cases']:
 run('compile-'+name,['-o',name+'.olean',name+'.lean'])
run('compile-driver',['NEP_Driver.lean'])
log=run('fixtures',['--run','NEP_Driver.lean','fixtures'])
rows=[json.loads(s) for s in re.findall(r'NEP_RESULT (\{[^\n]+\})',log)];assert len(rows)==10
expected={'NEP_Planted.matcher':['NEP_Planted.matchAx'],'NEP_Planted.viaPrivate':['NEP_Planted.privateAx'],'NEP_Planted.proof':['NEP_Planted.proofAx'],'NEP_Planted.viaAux':['NEP_Planted.auxAx'],'NEP_MutateMatch.matcher':[],'NEP_MutatePrivate.viaPrivate':[],'NEP_MutateProof.proof':[],'NEP_MutateAux.viaAux':[],'PV_D595_Cases.payload':['NEP_Planted.auxAx'],'PV_D595_Cases.proof':['NEP_Planted.proofAx']}
assert set(expected)=={r['root'] for r in rows}
reached={}
for row in rows:
 root=row['root'];assert row['equal'] and row['walked_axioms']==row['collect_axioms']==expected[root],row
 names=Path('NEP_fixtures_'+root+'_REACHABLE.txt').read_text().splitlines()
 assert len(names)==len(set(names))==row['reachable_constants'] and root in names
 reached[root]=names
assert any('matcher.match_' in n for n in reached['NEP_Planted.matcher'])
assert any(n.startswith('_private.') for n in reached['NEP_Planted.viaPrivate'])
assert any(n.endswith('NEP_Planted.hiddenAux') for n in reached['NEP_Planted.viaAux'])
assert 'NEP_Planted.proofAx' in reached['NEP_Planted.proof']
assert 'PV_D595_Cases.Box.mk' in reached['PV_D595_Cases.payload']
negative=run('missing-constant',['--run','NEP_Driver.lean','small'],1)
failures=[json.loads(s) for s in re.findall(r'NEP_FAILURE (\{[^\n]+\})',negative)]
assert len(failures)==1 and failures[0]['missing']=='PV_D595_Cases.deliberatelyMissing' and failures[0]['complete'] is False
assert 'missing reachable constant' in negative and 'NEP_RESULT ' not in negative
save('PREFLIGHT-RESULT.json',dict(status='PASS',scope_id=92070,fixture_results=rows,missing_constant_control=failures,original_cases=8,additional_success_cases=2,additional_expected_failure_cases=1,walker_unchanged=True,release_audit_run=False,steps=steps))
print('D595 PREFLIGHT PASS: original eight plus two positive cases and missing-constant control',flush=True)
