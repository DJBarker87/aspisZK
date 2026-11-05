from pathlib import Path
import subprocess,hashlib,json
E=Path(__file__).resolve().parent
ROOT=E.parents[1]
def git(*a):return subprocess.check_output(['git',*a],cwd=ROOT,text=True)
frozen=git('rev-parse','4bb3b3f5^{commit}').strip();head=git('rev-parse','HEAD').strip()
paths=['programs/r1-cost-probe/src/lib.rs','programs/r1-cost-probe/src/pool_route.rs','programs/r1-cost-probe/src/r1_pool_adapter.rs','programs/r1-cost-probe/src/r1_pool_adapter_owned.rs','crates/aspis-r1-cost-probe/src/verifier.rs','lean/F3T_Runtime.lean','lean/ARX_AdmittedRuntime.lean','evidence/l159-physical-20261107/NIN_ObserverPredicates.lean','evidence/l159-physical-20261107/NIN_ObserverFields.lean','evidence/experiment-law-20261106/NHZ_Realization.lean']
rows=[]
for p in paths:
 text=git('show',head+':'+p)
 rows.append(dict(path=p,revision=head,sha256=hashlib.sha256(text.encode()).hexdigest(),bytes=len(text.encode())))
patterns=[r'outer.?trace|nested.?events|literal.?flag|F3T_Runtime|RunView|ARU_Support',r'pub type Observer|fn observer|fn mark|fn digest|fn process_r1_cost_probe_instruction',r'fn stage1|fn stage2|fn process|fn admitted|set_return_data']
search=[]
for pattern in patterns:
 cmd=['git','grep','-n','-E',pattern,frozen,'--','programs/r1-cost-probe','crates/aspis-r1-cost-probe']
 r=subprocess.run(cmd,cwd=ROOT,text=True,capture_output=True)
 assert r.returncode in [0,1],r.stderr
 search.append(dict(command=cmd,exit=r.returncode,stdout=r.stdout,stderr=r.stderr))
result=dict(revision=head,frozen=frozen,tree_identity={p:dict(current=git('rev-parse',head+':'+p).strip(),frozen=git('rev-parse',frozen+':'+p).strip()) for p in ['crates','programs','Cargo.lock']},inputs=rows,search=search,limitation='Text census and inspected bodies locate no native joint exporter; absence of names alone is not a whole-program nonexistence proof. No Kani verdict or semantic proof is inferred.')
assert all(x['current']==x['frozen'] for x in result['tree_identity'].values())
(E/'NIP_SOURCE_CENSUS.json').write_text(json.dumps(result,indent=1)+'\n')
print('NIP source census: frozen trees identical; producer remains unidentified')
