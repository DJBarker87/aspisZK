from pathlib import Path
import sys
L=Path(__file__).resolve().parents[2]/'docs/research/v8-r0-zk-20261009/lean/R1Z'
s='''import R1Z.PV_RunJoin_IndexedResultModel20
import R1Z.PV_RunJoin_BankZero19
import R1Z.PV_RunJoin_CopyCertificate20
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ZeroCopy20
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_ValidatorZero19
open PV_RunJoin_CopyCertificate20
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
abbrev c := PV_RunJoin_BankZero19.certificate

theorem external_model : R0P.poseidonExternalLinear (liftA (K := M) s0) = liftA s1 := by
  obtain ⟨out,ho,hc,hm⟩ := PV_Src_ExternalModel.source (K := M) s0
  have h := PV_RunJoin_ValidatorZero19.external
  rw [PV_Src_ExternalReference.call_eq] at h
  have he : out = s1 := Result.ok.inj (ho.symm.trans h)
  exact (funext hm).symm.trans (congrArg liftA he)
#print axioms external_model

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) c.pre) i +
    (liftA c.absorption) i else (liftA c.pre) i) = liftA s0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
'''
for k in range(22):
 state='lead' if k==0 else f'c{k+1}'
 s+=f'''theorem step{k} : R0P.poseidonApplyRound ⟨{k},by decide⟩ (liftA (K := M) s{k+1}) = liftA s{k+2} :=
  PV_RunJoin_IndexedResultModel20.source _ _ {state}.property ⟨{k},by decide⟩ PV_RunJoin_ValidatorZero19.step{k}
#print axioms step{k}
'''
for n in range(11):
 s+=f'''theorem model{n+1} : R0Z.BuilderModel.blockIter (model c) {n+1} = liftA s{2*n+3} := by
  rw [iter_succ _ {n} (by decide)]
'''
 if n==0:
  s+='''  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA c.pre) (liftA c.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,external_model]
  have h0 : R0P.poseidonFullRound (liftA (K := M) s1) (R0P.poseidonExternalInitial 0) = liftA s2 := by
    exact (ar_init ⟨0,by decide⟩ (by decide) _).symm.trans step0
  have h1 : R0P.poseidonFullRound (liftA (K := M) s2) (R0P.poseidonExternalInitial 1) = liftA s3 := by
    exact (ar_init ⟨1,by decide⟩ (by decide) _).symm.trans step1
  exact (congrArg (fun x => R0P.poseidonFullRound x (R0P.poseidonExternalInitial 1)) h0).trans h1
'''
 else:
  s+=f'''  rw [model{n},trans_succ {n} (by decide) (by decide)]
  exact (congrArg (R0P.poseidonApplyRound ⟨{2*n+1},by decide⟩) step{2*n}).trans step{2*n+1}
'''
 s+=f'#print axioms model{n+1}\n'
s+='''theorem canon : ∀ n, n < 11 → Canonical (c.states (n+1)) := by
  intro n hn
  interval_cases n
'''+''.join(f'  · exact c{2*n+3}.property\n' for n in range(11))+'''#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model c) (n+1) = liftA (c.states (n+1)) := by
  intro n hn
  interval_cases n
'''+''.join(f'  · exact model{n+1}\n' for n in range(11))+'''#print axioms models

theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds c.pre c.absorption
      R0BlockCopies.write_block c.pre c.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer c canon models
#print axioms writer
end R1Z.PV_RunJoin_ZeroCopy20
'''
p=L/'PV_RunJoin_ZeroCopy20.lean'
if '--check' in sys.argv:assert p.read_text()==s
else:p.write_text(s)
print('symbolic zero certificate bridge; no chosen recurrence is reduced')
