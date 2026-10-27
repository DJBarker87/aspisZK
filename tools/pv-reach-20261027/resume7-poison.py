from pathlib import Path
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
for label,num,lam in [('Context',115,'fun _ _ => .fail e'),('Tag',234,'fun _ => .fail e'),('Encode',116,'fun _ => .fail e')]:
 s=(L/f'PV_RE_Client{label}7.lean').read_text();header=s[s.index('theorem client_to_'):s.index(' :\n    ∃ next,')];header=header.replace('theorem client_to_'+label.lower(),'theorem poisoned_client_failure')
 name=f'PV_RE_Poison{num}7';text=f'import R1Z.PV_RE_Client{label}7\nset_option autoImplicit false\nnoncomputable section\nnamespace R1Z.{name}\nopen Aeneas Aeneas.Std Result ProverRwFull PV_RE_RetryStep PV_RE_AttemptHashPrefix6 PV_RE_AttemptContext7 PV_RE_PublicPrefix6\nvariable [ExternalTypes]\ndef poison (D : ExternalFuns) (e : Error) : ExternalFuns :=\n  {{D with op{num} := {lam}}}\n'
 args='entropy pub compiled hash store state state1 secret guard entropy_prefix bytes digest serialization map_error first_hash'
 if label!='Context':args+=' context context_prefix'
 if label=='Encode':args+=' tag tag_prefix'
 text+=header+''' (e : Error) :
    @RealR1_client.prove_for_proof_accounts _ (poison D e) C entropy pub compiled hash store state =
      .fail e := by
'''+f'  obtain ⟨next,hn⟩ := PV_RE_Client{label}7.client_to_{label.lower()} (poison D e) {args}\n  rw [hn]\n  rfl\n#print axioms poison\n#print axioms poisoned_client_failure\n'
 h=header.replace('theorem poisoned_client_failure','theorem success_distinguishes')
 text+=h+''' (e : Error)
    (v : (core.result.Result prover.RetriedProof verifier.Error) × Store)
    (success : @RealR1_client.prove_for_proof_accounts _ D C
      entropy pub compiled hash store state = .ok v) :
    @RealR1_client.prove_for_proof_accounts _ (poison D e) C entropy pub compiled hash store state ≠
      @RealR1_client.prove_for_proof_accounts _ D C entropy pub compiled hash store state := by
'''+f'  rw [poisoned_client_failure D {args} e, success]\n  intro h\n  cases h\n#print axioms success_distinguishes\nend R1Z.{name}\n'
 (L/(name+'.lean')).write_text(text)
s=(L/'PV_RE_ClientContext7.lean').read_text();header=s[s.index('theorem client_to_'):s.index(' :\n    ∃ next,')].replace('theorem client_to_context','theorem excluded_poison_prefix')
text='''import R1Z.PV_RE_ClientContext7
import R1Z.PV_RE_ExcludedPoison
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ExcludedPrefixes7
open Aeneas Aeneas.Std Result ProverRwFull PV_RE_RetryStep PV_RE_AttemptHashPrefix6 PV_RE_AttemptContext7 PV_RE_PublicPrefix6
variable [ExternalTypes]
'''+header+'''
    (entry : PV_RE_ExcludedPoison.ExcludedField) (e : Error) :
    ∃ next, @RealR1_client.prove_for_proof_accounts _ (PV_RE_ExcludedPoison.poison D entry e) C
      entropy pub compiled hash store state = (D.op115 digest secret.mask_nonce >>= next) := by
  cases entry <;>
    exact PV_RE_ClientContext7.client_to_context _ entropy pub compiled hash store state state1 secret
      guard entropy_prefix bytes digest serialization map_error first_hash
#print axioms excluded_poison_prefix
end R1Z.PV_RE_ExcludedPrefixes7
'''
a=text.index('  cases entry <;>')
b=text.index('#print axioms excluded_poison_prefix',a)
proof='  cases entry with\n'
for field in [13,16,17,18,85,124,238]:
 proof+=f'  | op{field} =>\n      exact PV_RE_ClientContext7.client_to_context (PV_RE_ExcludedPoison.poison D .op{field} e)\n        entropy pub compiled hash store state state1 secret guard entropy_prefix bytes digest\n        serialization map_error first_hash\n'
text=text[:a]+proof+text[b:]
(L/'PV_RE_ExcludedPrefixes7.lean').write_text(text)
