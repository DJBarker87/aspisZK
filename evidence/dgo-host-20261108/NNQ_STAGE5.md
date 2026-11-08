Items 4/5 CLOSED: NNQ_Sim L013; NNQ_FirstDecoded L016; NNQ_Stage1
L020 (both stage1_sim and stage2_sim). Standard axioms only.
L011's historical import conflicts with RPz7 owner; replaced by the coherent
RPz7_GExq_OuterLower import, no shared source/object write. L012 fixes qualified
AdapterRw names. L014 exposes an omitted observer Result step in the mirror:
real trace preserves it using sim_bind/sim_lift; this is not a semantic leak.
L015's constructor metavariables falsely unified two dictionaries before rfl;
L016 applies the constructor first, proving only copy equality.
L017/L018's monolithic stage tactic class is retired. The remaining goals
are op43-free constant reads, isolated and proved in NNQ_StageLeaves L019;
L020 rewrites these named leaves and both outer stages pass.
No timeout or memory kill, no cap increase. Item6 is split into syntax laws,
prepared helpers, semantic helpers, and outer preparation before composition.
