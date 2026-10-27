"""Exact reserved-secret and material construction, with every callback reply explicit."""
from pathlib import Path
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
s=(L/'PV_RE_AfterPrefix1007.lean').read_text();head=s.split('theorem entered',1)[0].replace('PV_RE_AfterPrefix1007','PV_RE_AfterSuccess10')
args=s.split('theorem entered',1)[1].split(' :\n    ∃ next',1)[0]
args+='\n    (cleared : zeroize.Zeroizing (Array U8 32#usize))\n    (h7 : zeroize.Zeroizing.Insts.ZeroizeZeroize.zeroize Z secret.field_mask_entropy = .ok cleared)'
proof=s.split(' := by\n',1)[1].split('#print axioms',1)[0].replace('change ∃ next,','change')
proof=proof.replace('  exact ⟨_,rfl⟩','  change (zeroize.Zeroizing.Insts.ZeroizeZeroize.zeroize Z secret.field_mask_entropy >>= _) = _\n  rw [h7]\n  rfl')
text=head+'theorem success'+args+''' :
    ProverRwOuterAfterChecks.afterChecks inst secret hash binding context store =
      .ok (.Ok ({mask_nonce := secret.mask_nonce,precommit_binding := binding,
        reserved_context := context,leaf_salt_seed := secret.leaf_salt_seed,
        source_mask_seed := wrapped},material),store1) := by
'''+proof+'''#print axioms success
end R1Z.PV_RE_AfterSuccess10
'''
(L/'PV_RE_AfterSuccess10.lean').write_text(text)
