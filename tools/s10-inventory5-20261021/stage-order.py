#!/usr/bin/env python3
"""Map strict CFG witnesses to the current two-transaction semantic obligations."""
import argparse,hashlib,json
from pathlib import Path
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s10-inventory5-20261021'
def build():
    order=json.loads((B/'evidence/s10-inventory3-20261021/ordering-observations.json').read_text());facts=json.loads((E/'strict-order-map.json').read_text())['facts'];rows=[]
    for f in order['functions']:
        relevant=[p for p in facts if p['mode']==f['mode'] and p['path']==f['path'] and p['header']==f['header']];calls={c['line']:c for c in f['calls']}
        for p in relevant:
            rows.append(dict(mode=f['mode'],function=f['header'],body_sha256=f['body_sha256'],before=calls[p['before_line']],after=calls[p['after_line']],strict_theorem=p['strict_theorem'],status='CFG_STRICT_ORDER'))
    assert len(rows)==140
    return dict(schema='s10-pass5-twotx-stage-order-v1',model='AspisR1.OraclePortFrozen2.dV_frozen2',facts=rows,
        stages=[
          dict(source='TX1 parse_shape, canonical_scan, prepare',model='Guard, parseReached, queries and reconstructed input/opening view',residual='Parser/prepare/proof/public/challenge carriers and rejection order; parser and S1/S6 owners. Model Guard itself is not an extracted source function.'),
          dict(source='TX1 batch_merkle group 0: tree 0,1,2',model='batch p q batch0',residual='Exact mutable multiproof buffers, sorted leaves, duplicate/padding errors and child digests; multiproof owner.'),
          dict(source='TX1 geometry 0..10, query loop, pending-weight finish',model='C5 reached-ten accumulator used by checkpoint writer',residual='Whole reached-state S7/S8 simulation and fallible Vec allocation. No oracle effects may be invented/erased by a pure-state identification.'),
          dict(source='TX1 checkpoint proof/public/domain-body digests',model='checkpoint writer three ordered reads',residual='Same stored/public bytes and physical writer output, current prepared fields and saved accumulator; checkpoint/adapter owners.'),
          dict(source='Pool TX2 resume proof/public/domain-body digests',model='checkpoint resumer three ordered reads',residual='Actual account snapshots, short circuit/errors, byte reader adoption and saved fields; checkpoint/Pool owners.'),
          dict(source='TX2 batch_merkle group 1: tree 0,1,2',model='stage2: batch p q batch1',residual='Second group multiproof machine refinement and same proof/query/root carriers.'),
          dict(source='TX2 geometry 10..22, query loop, pending-weight finish, finish_relation',model='Pure resumed-twelve C5 recurrence inside checkpoint, followed by finish after batch1',residual='The model computes the pure twelve steps before batch1; the source computes them after batch1. To commute that state calculation, prove no oracle effects, reached-state totality and identical finish state; acceptance-only reasoning must preserve the complete accepted log. CFG block order alone does not prove this transport.')],
        source_order='OPEN: no frozen mutable source interpreter/Calls lowering is supplied by these CFG graphs',
        model_order='OPEN: no concrete shared source tree is supplied; the std-aware composition target is now dV_frozen2',
        source_coverage_instance='OPEN: current forty-label list is a diagnostic frontier, not a complete source site list',
        inputs={str(p.relative_to(R)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [B/'lean/OraclePortFrozen2Decision.lean',B/'lean/OraclePortFrozen2Checkpoint.lean',B/'evidence/s10-inventory3-20261021/ordering-observations.json',E/'strict-order-map.json']})
if __name__=='__main__':
    a=argparse.ArgumentParser();a.add_argument('--check',action='store_true');args=a.parse_args();x=build();raw=(json.dumps(x,indent=2,sort_keys=True)+'\n').encode();p=E/'stage-order.json'
    if args.check:assert p.read_bytes()==raw
    else:p.write_bytes(raw)
    print(json.dumps(dict(exit_status=0,strict_facts=len(x['facts']),source_order='OPEN',model_order='OPEN')))
