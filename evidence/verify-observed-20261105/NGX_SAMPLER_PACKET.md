# Sampler subcone association

Rows161/162/163 are three internal components of NGT's CLOSED scalar_k bridge,
not three duplicate proofs. NGX_NGT_REVALIDATION.json is a fresh read-only PASS
of NGT_validate.py:20 positive20 intended failing controls, deployed frozen
graph/lock/source, KMX and local records. NGT does not claim these extra row IDs;
NGX adds their explicit call-domain and model association here.

| Row | Actual native stages (NGT) | Exact same-value model association |
|---|---|---|
|162 qm31_div_pass|K021/022 arbitrary reverse cell; K029..034 arithmetic bounds/reconstruction; K037/038 reverse8 control|LPk_Step.Relation plus NGX_SamplerStages.pass_induction; pass_emitted is the actual cohort emitted pass, retaining all Results|
|161 qm31_digits|K015/016 LE32 init, K017/018 writeback, K039/040 four-pass control; row162 packet|NGX_SamplerStages.digits_induction and digits_emitted; NGT_NBA_Rho.four_digits connects the SAME four callbacks to rank(block)|
|163 qm31_sample|K019/020 complete four-coordinate packing, plus row161 packet|NGX_SamplerStages.sample = NGT_Reduction.scalar_k; NGX_SamplerJoin.total constructs the division/packing for EVERY block, without a success premise|

Domain: every borrowed block32, all8 input words u32; cell j1..8 and remainder<P
are derived from loop initialization/reverse control and previous remainder
bound; digit index0..3 from four-pass control; quotient and remainder casts fit
u32 by K029/K031 and the LPk bound laws. Packing uses the SAME four remainders
in c0.a,c0.b,c1.a,c1.b order. Each is<P, so the CLOSED CM31::new PacketDomain is
established without requiring arbitrary unrelated canonical input. Other field
constructors are type/record formation, not field multiplication.

No runtime digest occurs in these three pure functions. No oracle state or
independence assumption is added. The native enclosing transcript passes the
SAME read block to the sampler (NGX_K027/K028). Canonical output follows from
SamplerTransport.sample_total at that block. Frozen sampler source continuity
is checked by the reused NGT source/lock/metadata gate, not inferred from names.

ADMITTED by L064/L065/L066 and NGX_stage3_validate.py. Existing NGT inputs
are read-only; no sibling worktree or candidate is edited and no credit is
assigned to historical suspended static-log NBL_sampler_return.
