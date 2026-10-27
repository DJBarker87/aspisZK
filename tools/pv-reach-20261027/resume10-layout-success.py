"""Construct the exact source material record from ordered lower-level replies."""
from pathlib import Path
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
s=(L/'PV_RE_LayoutPrefix1007.lean').read_text();head=s.split('theorem prefix',1)[0].replace('PV_RE_LayoutPrefix1007','PV_RE_LayoutSuccess10')
args=s.split('theorem prefix',1)[1].split(' :\n    ∃ next',1)[0]
args+='\n    (h1 : alloc.vec.Vec aspis_core.field.QM31) (expander4 : Expander)\n    (h7 : aspis_prover.state_only_hiding.sample_mask_h1_padding expander3 inactive active = .ok (.Ok h1,expander4))'
# h1 is already a seed-reply proof; use padding as the data variable.
args=args.replace('(h1 : alloc.vec.Vec','(padding : alloc.vec.Vec').replace('.Ok h1,expander4','.Ok padding,expander4')
proof=s.split(' := by\n',1)[1].split('#print axioms',1)[0].replace('change ∃ next,','change')
proof=proof.replace('  exact ⟨_,rfl⟩','  change (aspis_prover.state_only_hiding.sample_mask_h1_padding expander3 inactive active >>= _) = _\n  rw [h7]\n  rfl')
text=head+'theorem success'+args+''' :
    aspis_prover.state_only_hiding.build_mask_material_for_layout inst hash binding context entropy store cells active =
      .ok (.Ok {c1 := c1,mask_only_c1 := columns,g := g,h1_padding := padding,mask_nonce := context.mask_nonce},store1) := by
'''+proof+'''#print axioms success
end R1Z.PV_RE_LayoutSuccess10
'''
(L/'PV_RE_LayoutSuccess10.lean').write_text(text)
