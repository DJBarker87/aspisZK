"""Full nonmutating offline audit. Emits JSON only; no network/host access.

python3 -B tools/resource-hierarchy-20261024/ResourceHierarchy_audit.py
No files written. Immutable historical inputs come exclusively from pinned git.
"""
import json
import sys
import os
import ResourceHierarchy_go as go
import ResourceHierarchy_tests as tests
from ResourceHierarchy_objects import Objects, BASE, ACTUAL, REV
from ResourceHierarchy_replay import replay

def compact(d):
    return {k:d[k] for k in ('allowed','error','estimated_total_bytes','projected_reserved_bytes','cap_ok','available_ok','legacy_nonreserve_gate_ok') if k in d}

def offline_guard(event,args):
    if event.startswith('socket.') or event in ('os.scandir','os.system','os.fork','os.posix_spawn'):
        raise RuntimeError('offline audit forbids '+event)
    if event=='subprocess.Popen' and args[1]!=['git','cat-file','--batch']:
        raise RuntimeError('offline audit forbids external command')
    if event=='open' and not isinstance(args[0],int):
        mode,flags=args[1:3]
        if (isinstance(mode,str) and any(x in mode for x in 'wax+')) or flags & (os.O_WRONLY|os.O_RDWR|os.O_CREAT|os.O_TRUNC):
            raise RuntimeError('nonmutating audit forbids writes')

def main():
    sys.addaudithook(offline_guard)
    objects=Objects()
    try:
        measured,original=replay(objects)
        validation=tests.run(objects,measured)
        s=measured['snapshots'];old=measured['original_legacy']
        a,b=(go.accounting(s[p]) for p in ('before','after'))
        decisions={}
        for size in (1,2,3,4,6,7,8):
            q=size*go.GIB
            d=go.evaluate(go.legacy_request(old,q),s['before'],s['after'],q,phase='prospective')
            assert 'error' not in d,d
            decisions[str(size)]=dict(**compact(d),physical_margin_bytes=min(a['mem_total'],b['mem_total'])-d['estimated_total_bytes'],
                strict_frontier_remaining_bytes=go.LIMIT-d['projected_reserved_bytes'],
                margin_above_7GiB_control_bytes=min(a['mem_total'],b['mem_total'])-(d['estimated_total_bytes']-7*go.GIB)-7*go.GIB)
        base=go.evaluate(go.legacy_request(old,go.GIB),s['before'],s['after'],go.GIB,phase='prospective')
        newcells=[]
        for envelope in base['envelope']:
            x=next(r for r in a['exclusive'] if r['path']==envelope['path'])
            y=next(r for r in b['exclusive'] if r['path']==envelope['path'])
            if x['negative_debt'] or y['negative_debt']:
                newcells.append(dict(envelope=envelope,before=x,after=y,
                    zero_credit_loss_against_positive_part_diagnostic=dict(
                        inactive=min(max(0,x['exclusive_stat']['inactive_file']),max(0,y['exclusive_stat']['inactive_file'])),
                        half_slab=min(max(0,x['exclusive_stat']['slab_reclaimable'])//2,max(0,y['exclusive_stat']['slab_reclaimable'])//2)),
                    note='diagnostic credit loss only; old gate DENIED so no old accepted reserve exists'))
        # Recorded ResourceStat historical pair accepted by old candidate: exact preservation.
        prefix='evidence/resource-slab-20261024/go-api/'
        historical={p:objects.json(prefix+'snapshot-'+p+'.json') for p in ('before','after')}
        legacy=objects.json(prefix+'legacy-snapshot.json');oldapi=objects.run(BASE+'ResourceStat_go.py')
        preservation={}
        for size in (1,2,3,4,6,7,8):
            q=size*go.GIB;lg=go.legacy_request(legacy,q)
            previous=oldapi['evaluate'](lg,historical['before'],historical['after'],q,phase='prospective')
            new=go.evaluate(lg,historical['before'],historical['after'],q,phase='prospective')
            assert 'error' not in previous and 'error' not in new
            for k in ('allowed','estimated_total_bytes','envelope','projected_reserved_bytes','cap_ok','available_ok'):
                assert previous[k]==new[k],k
            preservation[str(size)]=compact(new)
        fitness='/sys/fs/cgroup/system.slice/hausklar-fitness-worker.service'
        oldcell=next(d for d in oldapi['accounting'](historical['after'])['exclusive'] if d['path']==fitness)
        newcell=next(d for d in go.accounting(historical['after'])['exclusive'] if d['path']==fitness)
        assert oldcell['excess_over_current']==newcell['excess_over_current']==4096
        for k,v in oldcell.items():assert newcell[k]==v,(k,newcell[k],v)
        reused={p:objects.json(p) for p in ('evidence/resource-stat-20261024/tests-receipt.json','evidence/resource-actual-20261024/tests-receipt.json')}
        # Host capture metadata is reused, never measured by this audit.
        output=dict(schema='ResourceHierarchy-offline-audit-v1',status='PASS',adopted=False,
            immutable_revision=REV,current_headroom='UNKNOWN',new_host_reads=0,
            print_axioms='N/A; no formal work',original_replay=original,focused_validation=validation,
            counterfactual_reused_pair_only=decisions,newly_fully_charged_cells=newcells,
            before_accounting=a,after_accounting=b,pair_envelope=base['envelope'],
            root_residual_pair_bytes=[a['root_residual_bytes'],b['root_residual_bytes']],
            bounded_reserved_bytes=a['bounded_reserved_bytes'],os_control_bytes=7*go.GIB,
            total_pair_credit_bytes=sum(x['inactive_credit']+x['half_slab_credit'] for x in base['envelope']),
            total_pair_uncovered_reserve_bytes=sum(x['reserve'] for x in base['envelope']),
            recorded_preservation=preservation,old_4096_cell_preserved=True,
            historical_receipts_reused=reused,input_and_dependency_hashes=objects.pins,
            limits='Recorded-integer estimate, no error bound, no new identity gate, no actual GO or consumer validation')
        raw=json.dumps(output,sort_keys=True,indent=2)+'\n'
        assert len(raw.encode())<5_000_000
        print(raw,end='')
    finally:objects.close()

if __name__=='__main__':main()
