"""Read-only structural source check; never an extraction/refinement claim."""
from pathlib import Path
import hashlib,json,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin27-20261027'
rel='crates/aspis-statement/src/pool_v1/pair_forest_trace.rs'
s=(R/rel).read_text();a=s.index('pub fn compile_pool_v1_pair_forest_withdrawal_merged_c1_v1(');b=s.index('\n}',a)+2;body=s[a:b]
guard='''    if witness.change.value == 0
        || witness.change.value >= VALUE_LIMIT
        || public.amount.checked_add(witness.change.value) != Some(witness.input.pair.value)
    {
        return Err(PoolV1PairTraceErrorV1::Conservation);
    }'''
assert guard in body
assert body.index(guard)<body.index('    compile_forest_from_copies(')
rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip();baseline=subprocess.check_output(['git','show','d6bc54e213:'+rel])
assert baseline==(R/rel).read_bytes()
model='docs/research/100bit-spend-path-20261013/lean/SpendRelation.lean'
plus='docs/research/v8-r0-zk-20261009/lean/R1Z/BuilderSpendRelation.lean'
record=dict(classification='structural frozen native source inspection; not a claimed extracted wrapper theorem',revision=rev,path=rel,source_sha256=hashlib.sha256(s.encode()).hexdigest(),blob=subprocess.check_output(['git','rev-parse',rev+':'+rel],text=True).strip(),function=body,guard=guard,guard_precedes_compiler=True,unchanged_from_resume_head=True,model_source=model,plus_source=plus,semantic_candidate='R1Z.PV_RunJoin_SpendDomain27.admitted',consequence='Successful native withdrawal preparation requires nonzero change. A value-preserving encoding of the candidate has change.value=0 and cannot return a compilation, regardless of public hash encodings or preceding checks. Preceding checks may reject earlier; native control probe determines the observed error for the concrete data.')
(E/'source-guard.json').write_text(json.dumps(record,indent=2)+'\n')
print('Frozen withdrawal wrapper: zero-change rejection before core compiler; source unchanged')
