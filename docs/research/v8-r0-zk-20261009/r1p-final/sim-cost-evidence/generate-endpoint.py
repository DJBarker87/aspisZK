"""Copy the original headline statement verbatim, then append cost contracts."""
from pathlib import Path
root=Path(__file__).resolve().parents[2]
s=(root/'lean/R1Z/PrivacyR1HeadlineV2.lean').read_text()
start=s.index('theorem privacy_headline_v2\n');colon=s.index(' :\n    ZK_FSS',start);end=s.index(' := by',colon)
prefix=s[:s.index('theorem privacy_headline_v2_fibres')]
prefix=prefix.replace('import R1Z.PrivacyR1HeadlineWire2\nimport R1Z.PrivacyR1FinalProtocolCaller','import R1Z.PrivacyR1HeadlineV2\nimport R1Z.SimCostIdeal')
prefix=prefix.replace('namespace R1Z.PrivacyR1HeadlineV2','namespace R1Z.PrivacyR1HeadlineV2Sim')
a=prefix.index('/-!');b=prefix.index('set_option',a)
prefix=prefix[:a]+'''/-! Conditional efficiency extension. Every V2 privacy premise is retained.
The new prelude implementation and encoding bounds are explicit residuals;
this endpoint is not an unconditional simulator-efficiency closure. -/
'''+prefix[b:]
extra='''
local notation "simWire" => R1Z.PhaseLocalityBin.R1PhaseWire.toWire
  (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)
local notation "simProver" => R1Z.PhaseLocalityBin.R1PhaseProver.toProver
  (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)
local notation "simPredicate" => P_R1 (R0Z.ZkStatement.HonestProver.transport h) B hB
local notation "simulator" => simE (R0Z.ZkStatement.HonestProver.transport h) B outputs x
'''
binders=s[start:colon].replace('theorem privacy_headline_v2\n','theorem privacy_headline_v2_sim\n')
newbind='''
    (C L T : Nat)
    (sim_preparation : SimCostIdeal.Preparation simWire 8 eight_pos simPredicate x simulator C)
    (sim_sizes : ∀ (adv : (source).Adversary) (r : (source).IdealRand),
      SimCostIdeal.Sizes simWire L T adv
        (SimCostIdeal.prepare simWire 8 eight_pos simPredicate x simulator r))'''
conclusion=s[colon+3:end]
addition=''' ∧
    ∀ (adv : (source).Adversary) (r : (source).IdealRand),
      (SimCostIdeal.run simWire 8 eight_pos simPredicate x simulator C sim_preparation adv r).1 =
        (source).ideal simulator adv x r ∧
      (SimCostIdeal.run simWire 8 eight_pos simPredicate x simulator C sim_preparation adv r).2 ≤
        SimCostIdeal.coefficient C L T*((simWire).qmax+1)'''
body=''' := by
  constructor
  · exact PrivacyR1HeadlineV2.privacy_headline_v2 template input outputs x decode
      builder_premises R_commit_caller observer_program R_wire_builder_checker_D75_retry G_sim_R_wire
  · intro adv r
    constructor
    · exact SimCostIdeal.run_erase simWire 8 eight_pos simPredicate x simulator simProver
        (fun h' => VR1 h') C sim_preparation adv r
    · exact SimCostIdeal.run_linear simWire 8 eight_pos simPredicate x simulator C L T
        sim_preparation adv r (sim_sizes adv r)

#print axioms privacy_headline_v2_sim
end R1Z.PrivacyR1HeadlineV2Sim
'''
(root/'lean/R1Z/PrivacyR1HeadlineV2Sim.lean').write_text(prefix+extra+binders+newbind+' :\n    ('+conclusion.strip()+')'+addition+body)
