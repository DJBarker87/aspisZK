#!/usr/bin/env python3
"""Generate an explicit conditional adapter; never claim the missing model law."""
from pathlib import Path
import sys
root = Path(__file__).resolve().parents[1]
s = (root/'lean/R1Z/PrivacyR1FinalProtocol.lean').read_text()
start = s.index('theorem privacy_R1_protocol\n')
end = s.index(' := by\n', start)
statement = s[start:end].replace('theorem privacy_R1_protocol\n', 'theorem privacy_R1_protocol_history_of_model_laws\n')
model = '(fsR1P (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver 8 (by decide) (P_R1 h.transport B hB) (fun h\' => VR1 h\'))'
marker = '    (R_wire_builder_checker_D75_retry :'
i = statement.index(marker)
new = f'''    (realBad : source.Adversary → h.Instance → Fin 8 → {model}.RealRand → Prop)
    (idealBad : source.Adversary → Fin 8 → {model}.IdealRand → Prop)
    (real_model_history_law : ∀ adv w, h.public w = x.1 →
      ∀ i, eventMass (realBad adv w i) ≤ scanProbability)
    (ideal_model_history_law : ∀ adv i, eventMass (idealBad adv i) ≤ scanProbability)
'''
statement = statement[:i]+new+statement[i:]
statement = statement.replace('→ ScanCoupling\n','→ ModelExecutionJoin\n').replace('(G_sim_R_wire : ∀ adv : source.Adversary, ScanCoupling\n','(G_sim_R_wire : ∀ adv : source.Adversary, ModelExecutionJoin\n')
realend = ' (RomObserverBin.observerMap source observer_program adv) x w))'
assert realend in statement
statement = statement.replace(realend, ' (RomObserverBin.observerMap source observer_program adv) x w) (realBad adv w))')
idealend = '(RomObserverBin.observerMap source observer_program adv) x (simE h.transport B outputs x))) :'
assert idealend in statement
statement = statement.replace(idealend, '(RomObserverBin.observerMap source observer_program adv) x (simE h.transport B outputs x)) (idealBad adv)) :')
context = s[s.index('open R0P'):s.index('/-- The eight address families')]
context = context[:context.index('variable (seed :')]
context = context.replace('open R1Z.PhaseProtocolInstanceBin R1Z.PrivacyR1Final','open R1Z.PhaseProtocolInstanceBin R1Z.PrivacyR1Final R1Z.QueryScanHistorySplit')
proof = ''' := by
  exact PrivacyR1FinalProtocol.privacy_R1_protocol base h B outputs x seed hB hpub
    builder_refinement_D46_D51 cF R_commit_equal_fibres L₁ L₂ R_commit_exhaustion
    R_commit_counter₁ R_commit_counter₂ R_commit_stream₁ R_commit_stream₂
    R_wire_coin_carrier R_wire_D80_batches R_wire_D80_ordered_log R_commit_cell_count
    R_commit_blocks₁ R_commit_blocks₂ source observer_program
    (fun adv w hw => (R_wire_builder_checker_D75_retry adv w hw).toScanCoupling
      (real_model_history_law adv w hw))
    (fun adv => (G_sim_R_wire adv).toScanCoupling (ideal_model_history_law adv))

#print axioms privacy_R1_protocol_history_of_model_laws

/-- The independent ideal-model law is available at the exact constructed
experiment. The real shared-ROM law is deliberately not asserted here. -/
theorem constructed_ideal_model_history_law
    (seed : R1ProverP K CommitHandle Aux F
      (wire base ((base.pubBytes x).length) h B outputs x).toWire)
    (hB : R0Z.K4.PackField B) (i : Fin 8) :
    eventMass (fun r : (fsR1P
      (wire base ((base.pubBytes x).length) h B outputs x).toWire
      (prover base ((base.pubBytes x).length) h B outputs x seed).toProver
      8 (by decide) (P_R1 h.transport B hB) (fun h' => VR1 h')).IdealRand =>
      QueryScanIdealHistory.selectedBad i r) ≤ scanProbability := by
  exact QueryScanIdealHistory.selected_bad_mass i

#print axioms constructed_ideal_model_history_law
end R1Z.PrivacyR1FinalProtocolHistory
'''
specialized = statement.replace('privacy_R1_protocol_history_of_model_laws', 'privacy_R1_protocol_history')
specialized = '\n'.join(line for line in specialized.split('\n')
    if not line.startswith('    (idealBad :') and not line.startswith('    (ideal_model_history_law :'))
specialized = specialized.replace('(idealBad adv)', '(QueryScanIdealHistory.selectedBad)')
specialized += ''' := by
  exact privacy_R1_protocol_history_of_model_laws base h B outputs x seed hB hpub
    builder_refinement_D46_D51 cF R_commit_equal_fibres L₁ L₂ R_commit_exhaustion
    R_commit_counter₁ R_commit_counter₂ R_commit_stream₁ R_commit_stream₂
    R_wire_coin_carrier R_wire_D80_batches R_wire_D80_ordered_log R_commit_cell_count
    R_commit_blocks₁ R_commit_blocks₂ source observer_program realBad
    (fun _ => QueryScanIdealHistory.selectedBad) real_model_history_law
    (fun _ i => QueryScanIdealHistory.selected_bad_mass i)
    R_wire_builder_checker_D75_retry G_sim_R_wire

#print axioms privacy_R1_protocol_history
'''
proof = proof.replace('end R1Z.PrivacyR1FinalProtocolHistory', specialized + '\nend R1Z.PrivacyR1FinalProtocolHistory')
out = '''import R1Z.PrivacyR1FinalProtocol
import R1Z.QueryScanHistorySplit
import R1Z.QueryScanIdealHistory
import R1Z.QueryScanSharedHistoryObstruction

/-! Conditional adapter only. Fixed model events allow execution-only joins.
Their real-model mass law is NOT discharged: the per-history demand is false
on repeated shared-ROM reads. See the compiled obstruction and report.
This module deliberately does not assert the requested unconditional endpoint. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PrivacyR1FinalProtocolHistory
'''+context+statement+proof
target = root/'lean/R1Z/PrivacyR1FinalProtocolHistory.lean'
if '--check' in sys.argv:
    assert target.read_text() == out, 'history endpoint differs from generator'
else:
    target.write_text(out)
