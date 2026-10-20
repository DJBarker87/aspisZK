#!/usr/bin/env python3
"""Audit retained candidate proof inventory; this is not a semantic composition proof."""
from pathlib import Path
import argparse, hashlib, json, resource, subprocess, sys, time
start=time.monotonic()
parser=argparse.ArgumentParser();parser.add_argument('--partial',action='store_true');args=parser.parse_args()
tool=Path(__file__).resolve().parent;area=tool.parents[1];repo=tool.parents[4];ev=area/'evidence/cu-equivalence-20261019'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
git=lambda *xs:subprocess.check_output(['git','-C',str(repo),*xs],text=True).strip()
rows=[
(1,'gamma reuse','3ab4faf7f','GAMMA-CANDIDATE1-FINAL.json',[34201,34243],[0,0]),
(2,'profiling removal','190e1779c','PROFILING-CANDIDATE2-FINAL.json',[10992,10992],[13201,13201]),
(3,'fixed S2 groups','d631a90ec','S2-CANDIDATE3-FINAL.json',[0,0],[40517,40520]),
(4,'delayed base dots','d11f9b2fc','DELAYED-CANDIDATE4-FINAL.json',[28221,28252],[33880,33932]),
(5,'canonical dots','e58b87665','CANONICAL-CANDIDATE5-COMPONENTS.json',[11273,11286],[11617,11630]),
(6,'public decode reuse','e5a93db5c','CANDIDATE6-COMPLETION.json',[7418,7472],[0,0]),
(7,'query geometry reuse','2aa1b879c','GEOMETRY-CANDIDATE7-FINAL.json',[780,791],[947,957]),
(10,'fixed608prefix','225a3736d','PREFIX-CANDIDATE10-FINAL.json',[5620,5620],[6744,6744]),
(12,'rho residues','16a39d2a8','RHO-CANDIDATE12-FINAL.json',[42693,42746],[51250,51356]),
(14,'Libra factorization','39c2971dd','LIBRA-CANDIDATE14-FINAL.json',[0,0],[33363,33427])]
entries=[];all_receipts={};missing=[]
for number,label,revision,name,stage,settlement in rows:
    candidate=git('rev-parse',revision);parent=git('rev-parse',revision+'^');path=ev/name
    if not path.is_file():
        missing.append(number);continue
    data=json.loads(path.read_text());assert data['candidate']==candidate,(number,'candidate')
    assert git('rev-parse',data.get('parent',data.get('reference_parent')))==parent,(number,'parent')
    selected={}
    def visit(value):
        if isinstance(value,dict):
            if isinstance(value.get('attempt'),str):
                rp=ev/value['attempt']/'receipt.json'
                if rp.is_file():
                    r=json.loads(rp.read_text());assert r['exit_status']==0,rp
                    source=rp.parent/'source.lean'
                    if source.is_file():assert sha(source)==r['source_sha256'],source
                    module=r.get('module')
                    if module:
                        local=area/'lean'/(module.replace('.','/')+'.lean')
                        if not local.is_file():local=area/'lean'/(module+'.lean')
                        if local.is_file():assert sha(local)==r['source_sha256'],(number,module,'stale source')
                    log=r.get('print_axioms_output','');assert log and not any(x in log for x in ['sorryAx','ofReduceBool','error:']),rp
                    for field in ['command','source_revision','features','wall_seconds','peak_rss_kib','process_swaps']:
                        assert field in r,(rp,field)
                    selected[value['attempt']]={'receipt':str(rp.relative_to(repo)),'receipt_sha256':sha(rp),'module':module,'source_sha256':r['source_sha256'],'object_sha256':r.get('object_sha256'),'print_axioms':log}
                    all_receipts[value['attempt']]=selected[value['attempt']]
            for child in value.values():visit(child)
        elif isinstance(value,list):
            for child in value:visit(child)
    visit(data)
    # Candidate6 stores its completed source-consuming receipts by path/hash,
    # rather than embedding attempt fields. Its dedicated checker audits them.
    if number!=6:assert selected,(number,'missing selected release receipts')
    entries.append({'candidate_number':number,'label':label,'candidate':candidate,'parent':parent,'report':str(path.relative_to(repo)),'report_sha256':sha(path),'stage1_saving_cu':stage,'settlement_saving_cu':settlement,'selected_receipts':selected,'boundary':'See exact report; source/runtime interpretations remain explicit.'})
assert args.partial or not missing,('unfinished candidate reports',missing)
assert git('diff','39c2971dd','--','crates','programs')=='','production changed'
u=resource.getrusage(resource.RUSAGE_SELF)
report={'status':'PARTIAL_INVENTORY' if missing else 'TEN_RETAINED_CANDIDATE_REPORTS_AND_PINS_AUDITED','source_equivalence_composition_claimed_by_this_inventory':False,'reference_revision':git('rev-parse','f458169f7'),'production_revision':git('rev-parse','39c2971dd'),'missing_candidates':missing,'candidates':entries,'distinct_selected_receipts':len(all_receipts),'audit':{'command':[sys.executable,*sys.argv],'revision':git('rev-parse','HEAD'),'features':'metadata/source/receipt audit only','exit':0,'wall_seconds':time.monotonic()-start,'peak_rss_bytes':u.ru_maxrss if sys.platform=='darwin' else u.ru_maxrss*1024,'process_swaps':u.ru_nswap,'print_axioms':'N/A Python audit; exact Lean outputs retained above'}}
(ev/'RETAINED-EQUIVALENCE-INVENTORY.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'status':report['status'],'reported_candidates':len(entries),'missing':missing,'selected_receipts':len(all_receipts)}))
