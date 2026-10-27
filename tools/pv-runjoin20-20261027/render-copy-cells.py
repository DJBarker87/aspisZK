from pathlib import Path
import sys
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
for j in range(81):
 math='PV_RunJoin_FixtureHashModel' if j<6 else 'PV_RunJoin_PathModel16' if j<30 else 'PV_RunJoin_OutputModel16'
 group=(j//9)*9;c=f'PV_RunJoin_BankCell{j:02}19';v=f'PV_RunJoin_ValidatorCell{j:02}19';name=f'PV_RunJoin_CopyCell{j:02}20'
 s=f'''import R1Z.PV_RunJoin_CopyCertificate20
import R1Z.PV_RunJoin_BankCells{group:02}19
set_option autoImplicit false
noncomputable section
namespace R1Z.{name}
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open {math}

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) {c}.certificate.pre) i +
    (liftA {c}.certificate.absorption) i else (liftA {c}.certificate.pre) i) = s_{j}_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
'''
 for n in range(11):
  s+=f'''theorem model{n+1} : R0Z.BuilderModel.blockIter (model {c}.certificate) {n+1} = s_{j}_{2*n+3} := by
  rw [iter_succ _ {n} (by decide)]
'''
  if n==0:
   s+=f'''  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA {c}.certificate.pre) (liftA {c}.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_{j}_1,round_{j}_2]
  exact round_{j}_3
'''
  else:
   s+=f'''  rw [model{n},trans_succ {n} (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨{2*n+1},by decide⟩
    (R0P.poseidonApplyRound ⟨{2*n},by decide⟩ s_{j}_{2*n+1}) = _
'''
   for k in [2*n,2*n+1]:
    state=f's_{j}_{k+1}'
    lemma='ar_init' if k<4 else 'ar_int' if k<18 else 'ar_fin'
    args='(by decide)' if k<4 else '(by decide) (by decide)'
    s+=f'  have step{k} : R0P.poseidonApplyRound ⟨{k},by decide⟩ {state} = s_{j}_{k+2} :=\n    ({lemma} ⟨{k},by decide⟩ {args} {state}).trans round_{j}_{k+2}\n'
   s+=f'  exact (congrArg (R0P.poseidonApplyRound ⟨{2*n+1},by decide⟩) step{2*n}).trans step{2*n+1}\n'
  s+=f'#print axioms model{n+1}\n'
 s+=f'''theorem canon : ∀ n, n < 11 → Canonical ({c}.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
'''+''.join(f'  · exact {v}.canon{2*n+3}\n' for n in range(11))+'''#print axioms canon
'''
 s+=f'''theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model {c}.certificate) (n+1) =
    liftA ({c}.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
'''+''.join(f'  · exact model{n+1}.trans {v}.lift{2*n+3}.symm\n' for n in range(11))+'''#print axioms models
'''
 s+=f'''theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds {c}.certificate.pre {c}.certificate.absorption
      R0BlockCopies.write_block {c}.certificate.pre {c}.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = ({c}.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.{name}
'''
 p=L/(name+'.lean') if j==0 else R/'evidence/pv-runjoin20-20261027/cell-drafts'/(name+'.lean.txt')
 if '--check' in sys.argv:assert p.read_text()==s
 else:p.write_text(s)
print('81 symbolic per-cell model bridges generated; no recurrence evaluated')
