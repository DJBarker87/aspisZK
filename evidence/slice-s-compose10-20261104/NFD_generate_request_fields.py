from pathlib import Path
E=Path(__file__).resolve().parent
common=['(get p.pool j).val','(get p.deployment_domain j).val','p.anchor_sequence.val','(get p.anchor_root i).val','(get p.nullifier i).val','p.asset_id.val','(get p.change_commitment i).val']
for slot in range(14):
 if slot<3:expr='(get s.'+['verifier_profile','verifier_release','pool_program'][slot]+' j).val'
 else:
  l='1' if slot==3 else common[slot-4] if slot<11 else '(get p.recipient_commitment i).val' if slot==11 else '0'
  r='2' if slot==3 else common[slot-4] if slot<11 else 'p.amount.val' if slot==12 else '(get p.destination_token_account j).val' if slot==13 else '0'
  expr='match s.«public» with\n | .PrivateTransfer p => '+l+'\n | .Withdrawal p => '+r
 text='''import NFD_RequestProjection
set_option autoImplicit false
noncomputable section
namespace NFD_RequestField'''+f'{slot:02}'+'''
open Aeneas Aeneas.Std NFD_RequestProjection
open NEU_PublicProjections (get)
def expected (s : Request) (i : Fin 8) (j : Fin 32) : Nat :=
 '''+expr+'''
theorem alignment (s : Request) (i : Fin 8) (j : Fin 32) :
    project s ⟨'''+str(slot)+''',by decide⟩ i j=expected s i j := by
'''+('  rfl\n' if slot<3 else '  cases h : s.«public» <;> simp only [project,expected,h] <;> rfl\n')+'''
#print axioms alignment
end NFD_RequestField'''+f'{slot:02}'+'\n'
 (E/f'NFD_RequestField{slot:02}.lean').write_text(text)
