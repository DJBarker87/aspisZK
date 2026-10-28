"""Keep dictionary opaque in the generic source proof, then install source-selected leaves."""
from pathlib import Path
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
s=(L/'PV_RE_AttemptReserve7.lean').read_text();head=s.split('theorem attempt_to_reserve',1)[0].replace('PV_RE_AttemptReserve7','PV_RE_AttemptClone10')
args=s.split('theorem attempt_to_reserve',1)[1].split(' :\n    ∃ next',1)[0]
extra='''
    (store1 : Store)
    (reserved : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
    (material : aspis_prover.state_only_hiding.StateOnlyMaskMaterial)
    (reservation : @aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.reserve_and_build_pool_v1_pair_forest_mask_material_v1
      _ D Store
      (@aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore _ D)
      secret hash binding context store = .ok (.Ok (reserved,material),store1))
    (mapped : D.op12 (BuiltinFnOnce aspis_prover.state_only_hiding.StateOnlyMaskBuildError verifier.Error)
      (.Ok (reserved,material)) prover.mask_error = .ok (.Ok (reserved,material)))'''
proof=s.split(' := by\n',1)[1].split('#print axioms',1)[0].replace('  exact ⟨_,rfl⟩','''  rw [reservation]
  change ∃ next, (D.op12 (BuiltinFnOnce aspis_prover.state_only_hiding.StateOnlyMaskBuildError verifier.Error)
    (.Ok (reserved,material)) prover.mask_error >>= _) = _
  rw [mapped]
  exact ⟨_,rfl⟩''')
text=head+'theorem entered'+args+extra+''' :
    ∃ next, @prover.prove_masked_attempt _ D pub compiled variant hash secret store =
      (D.op231 compiled.semantic_c1 >>= next) := by
'''+proof+'''#print axioms entered
end R1Z.PV_RE_AttemptClone10
''';(L/'PV_RE_AttemptClone10.lean').write_text(text)
s=(L/'PV_RE_ClientClone10.lean').read_text().replace('R1Z.PV_RE_MaskedClone10\n','R1Z.PV_RE_MaskedClone10\nimport R1Z.PV_RE_AttemptClone10\n').replace('namespace R1Z.PV_RE_ClientClone10','namespace R1Z.PV_RE_ClientCloneB10').replace('end R1Z.PV_RE_ClientClone10','end R1Z.PV_RE_ClientCloneB10')
a=s.index('  unfold prover.prove_masked_attempt\n');b=s.index('#print axioms entered',a)
s=s[:a]+'''  exact PV_RE_AttemptClone10.entered D pub compiled .S2 hash secret store
    bytes digest serialization hm first_hash context hc 2#u8 ht
    (ProverRwOuterEncode.value context) he binding second_hash
    store1 reserved material reservation (by rfl)
'''+s[b:];(L/'PV_RE_ClientCloneB10.lean').write_text(s)
