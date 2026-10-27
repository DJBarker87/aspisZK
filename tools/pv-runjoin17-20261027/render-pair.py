from pathlib import Path
import re,sys
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z';data=(L/'PV_RunJoin_OutputData16.lean').read_text()
s='''import R1Z.PV_RunJoin_OutputCell3917
import R1Z.PV_RunJoin_OutputCell4017
import R1Z.PV_RunJoin_NodeValue17
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OutputPair17
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
open PV_RunJoin_ReferenceFixtureResults
local notation "M" => PV_RunJoin_FixtureRecords.M
attribute [local irreducible] R0P.nodeCompress
'''
for label,cell in [('transfer',39),('withdrawal',40)]:
 xs=list(map(int,re.search(rf'def s_{cell}_23 .*? := !\[(.*?)\]',data)[1].split(',')))[:8]
 s+=f'def {label}Pair : Array U32 8#usize := Array.make 8#usize ['+','.join(str(x)+'#u32' for x in xs)+']\n'
 left=f'PV_RunJoin_RecordedTransfer.publicRecord.recipient_commitment' if label=='transfer' else 'PV_RunJoin_RecordedWithdrawal.publicRecord.change_commitment'
 right='PV_RunJoin_RecordedTransfer.publicRecord.change_commitment' if label=='transfer' else 'ZERO8'
 start=list(map(int,re.search(rf'def s_{cell}_0 .*? := !\[(.*?)\]',data)[1].split(',')))
 lvec='!['+','.join(map(str,start[:8]))+']';rvec='!['+','.join(map(str,start[8:15]+[(start[15]-0x41531005)%2147483647]))+']';out='!['+','.join(map(str,xs))+']'
 s+=f'''theorem {label}_node : node_digest_r {left} {right} = ok {label}Pair := by
  apply PV_RunJoin_NodeValue17.source
  · intro j hj
    try (with_unfolding_all simp only [ZERO8,Array.repeat])
    interval_cases j <;> decide
  · intro j hj
    try (with_unfolding_all simp only [ZERO8,Array.repeat])
    interval_cases j <;> decide
  · have hl : digK (K := M) {left} = {lvec} := by
      try (with_unfolding_all simp only [ZERO8,Array.repeat])
      funext i; fin_cases i <;> rfl
    have hr : digK (K := M) {right} = {rvec} := by
      try (with_unfolding_all simp only [ZERO8,Array.repeat])
      funext i; fin_cases i <;> rfl
    have ht : digK (K := M) {label}Pair = {out} := by
      try (with_unfolding_all simp only [ZERO8,Array.repeat])
      funext i; fin_cases i <;> rfl
    rw [hl,hr,ht]
    exact PV_RunJoin_OutputModel16.node_{cell}
#print axioms {label}_node

theorem {label}_raw : out_pair_r {label}Witness {label}Public = ok {label}Pair := by
  rw [out_pair_r]
'''
 if label=='transfer':s+='''  change (do
    let r ← recip_dr transferWitness transferPublic
    let c ← change_dr transferWitness transferPublic
    node_digest_r r c) = _
  rw [PV_RunJoin_OutputChecks16.recipient_raw,PV_RunJoin_OutputChecks16.transfer_change_raw]
'''
 else:s+='''  change (do
    let c ← change_dr withdrawalWitness withdrawalPublic
    node_digest_r c ZERO8) = _
  rw [PV_RunJoin_OutputChecks16.withdrawal_change_raw]
'''
 s+=f'''  simp only [bind_tc_ok]
  exact {label}_node
#print axioms {label}_raw

theorem {label} : CopyRecords.output_pair ⟨{label}Witness,{label}Public⟩ = ok {label}Pair := by
  rw [CopyRecords.output_pair,{label}_raw]
  with_unfolding_all rfl
#print axioms {label}
'''
s+='end R1Z.PV_RunJoin_OutputPair17\n';p=L/'PV_RunJoin_OutputPair17.lean'
if '--check' in sys.argv:assert p.read_text()==s
else:p.write_text(s)
