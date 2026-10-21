from pathlib import Path
root=Path(__file__).resolve().parents[2]
s=(root/'lean/R1Z/PrivacyR1Headline.lean').read_text()
opens=s[s.index('open R0P'):s.index('variable {CommitHandle')]
opens=opens.replace('local notation "K" => AspisWideTower.WideExact','')
preamble='''import R1Z.PrivacyR1AcctModel

/-! Accounting-specialized headline. All decoder/execution joins are retained.
The source experiment here is the constructed finite binary-ROM experiment. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PrivacyR1HeadlineAcct
'''+opens+'''
open R1Z.PrivacyR1Headline
local notation "K" => PrivacyR1AcctBasis.K
local notation "F" => PrivacyR1AcctBasis.F
local notation "B" => PrivacyR1AcctBasis.basis
local notation "hB" => PrivacyR1AcctBasis.packing_laws
local notation "L₁" => PrivacyR1AcctModel.L₁
local notation "L₂" => PrivacyR1AcctModel.L₂
attribute [local irreducible] ProverCommitSourceDecoder.L₁ ProverCommitSourceDecoder.L₂
variable {CommitHandle Aux : Type}
variable (template : R1Wire K CommitHandle Aux)
    (log : (RIdx → OracleAnswer) → (Fin 3 → OracleAnswer) →
      View K CommitHandle Aux R1Bat → Challenges K → List (List UInt8 × OracleAnswer))
local notation "base" => PrivacyR1AcctModel.base template log
variable (h : HonestProver K)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle)
variable (decode : (Fin PrivacyR1AcctModel.E₁ → OracleAnswer) →
    (Fin PrivacyR1AcctModel.E₂ → OracleAnswer) → Option (Tape K F))
    (fib : Challenges K → Fin 3 → Finset Fib)
    (opens : Challenges K → List (Fin 3 ⊕ RIdx))
local notation "seed" => PrivacyR1AcctModel.seed
  (wire base ((base.pubBytes x).length) h B outputs x).toWire decode fib opens
local notation "source" => fsR1P
  (wire base ((base.pubBytes x).length) h B outputs x).toWire
  (prover base ((base.pubBytes x).length) h B outputs x seed).toProver
  8 (by decide) (P_R1 h.transport B hB) (fun h' => VR1 h')
local notation "coins" => PrivacyR1AcctModel.wire_coins template log h outputs x

instance real_fintype : Fintype source.RealRand := inferInstance
instance real_nonempty : Nonempty source.RealRand := inferInstance
instance ideal_fintype : Fintype source.IdealRand := inferInstance
instance ideal_nonempty : Nonempty source.IdealRand := inferInstance

'''
a=s.index('theorem privacy_headline\n'); b=s.index(' := by\n',a)
sig=s[a:b]
# Remove binders using balanced parenthesis/bracket scanning.
def remove_binder(text,name):
    start=text.index('('+name+' :') if '('+name+' :' in text else text.index('['+name+']')
    if text[start]=='[': return text[:start]+text[start+len(name)+2:]
    depth=0
    for end in range(start,len(text)):
        if text[end]=='(': depth+=1
        if text[end]==')':
            depth-=1
            if depth==0: return text[:start]+text[end+1:]
    raise ValueError(name)
for name in ['seed','hB','R_commit_counter₁','R_commit_counter₂','R_commit_stream₁','R_commit_stream₂','R_wire_coin_carrier','R_commit_cell_count','R_commit_blocks₁','R_commit_blocks₂','source']:
    sig=remove_binder(sig,name)
sig=sig.replace('(L₁ L₂ : ℕ) ','')
for name in ['Fintype source.RealRand','Nonempty source.RealRand','Fintype source.IdealRand','Nonempty source.IdealRand']:
    sig=remove_binder(sig,name)
sig=sig.replace('R_wire_coin_carrier.symm','coins.symm').replace('theorem privacy_headline','theorem privacy_headline_acct')
body=''' := by
  exact PrivacyR1Headline.privacy_headline base h B outputs x seed hB builder_premises
    cF R_commit_quotient_fibres L₁ L₂ R_commit_exhaustion
    (Nat.le_of_lt PrivacyR1AcctModel.counter₁) (Nat.le_of_lt PrivacyR1AcctModel.counter₂)
    PrivacyR1AcctModel.stream₁ PrivacyR1AcctModel.stream₂
    coins R_wire_D80_batches R_wire_D80_ordered_log
    PrivacyR1AcctModel.cell_count PrivacyR1AcctModel.blocks₁ PrivacyR1AcctModel.blocks₂
    source observer_program R_wire_builder_checker_D75_retry G_sim_R_wire

#print axioms real_fintype
#print axioms real_nonempty
#print axioms ideal_fintype
#print axioms ideal_nonempty
#print axioms privacy_headline_acct
end R1Z.PrivacyR1HeadlineAcct
'''
text=preamble+sig+body
text=text.replace('local notation "source" =>', 'theorem eight_pos : 0 < (8 : ℕ) := by decide\nlocal notation "source" =>').replace('(by decide)', 'eight_pos')
text=text.replace('#print axioms real_fintype', '#print axioms eight_pos\n#print axioms real_fintype')
text=text.replace('base.pubBytes x', 'R1Wire.pubBytes base x')
text=text.replace('(wire base ((R1Wire.pubBytes base x).length) h B outputs x).toWire', '(R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base ((R1Wire.pubBytes base x).length) h B outputs x))')
text=text.replace('(prover base ((R1Wire.pubBytes base x).length) h B outputs x seed).toProver', '(R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base ((R1Wire.pubBytes base x).length) h B outputs x seed))')
text=text.replace('((R1Wire.pubBytes base x).length)', '(List.length (R1Wire.pubBytes base x))').replace('h.transport', '(R0Z.ZkStatement.HonestProver.transport h)')
text=text.replace('source.RealRand','(source).RealRand').replace('source.IdealRand','(source).IdealRand').replace('source.Adversary','(source).Adversary').replace('coins.symm','(coins).symm')
text='\n'.join(l.rstrip() for l in text.splitlines() if l.strip())+'\n'
(root/'lean/R1Z/PrivacyR1HeadlineAcct.lean').write_text(text)
