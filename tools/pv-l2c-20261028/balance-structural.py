"""Fail-closed structural binding of the QM31 balance cut (K-1 substitute).
This binds successful balance on length-1024 tables, not the honest caller.
"""
from pathlib import Path
import json,re,hashlib,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-l2c-20261028/resume-d355'
def norm(s):return re.sub(r'\s+','',s)
def take(path,name):
 s=(R/path).read_text();a=re.search(r'\bfn '+name+r'\b',s).start();a=s.index('{',a)+1;b=a;depth=1
 while depth:
  depth+=(s[b]=='{')-(s[b]=='}');b+=1
 return s[a:b-1]
n='crates/aspis-prover/src/state_only_hiding.rs';r='crates/aspis-prover/src/prover_commit_reference.rs'
expected={
(n,'balance_qm31_copy_inactive'):'''let rows=STATE_ONLY_POSEIDON_TRACE_ROWS;
if table.len()!=STATE_ONLY_POSEIDON_TRACE_ROWS || active[dependent] {return Err(StateOnlyMaskBuildError::TraceShape);}
let sum=sum_qm31_copy_inactive(table,dependent,active);let value=QM31::ZERO.sub(sum);table[dependent]=value;Ok(())''',
(n,'sum_qm31_copy_inactive'):'''let rows=STATE_ONLY_POSEIDON_TRACE_ROWS;let mut sum=QM31::ZERO;let mut row=0;
while row<rows {sum=inactive_qm31_step(sum,table,dependent,active,row);row+=1;}sum''',
(n,'inactive_qm31_step'):'''if !active[row] && row!=dependent {sum.add(table[row])} else {sum}''',
(r,'balance_qm31_owned'):'''if table.len()!=1024 || active[dependent] {return (Err(StateOnlyMaskBuildError::TraceShape),table);}
let sum=balance_qm31_rows(&table,dependent,active,0,aspis_core::field::QM31::ZERO);
table[dependent]=aspis_core::field::QM31::ZERO.sub(sum);(Ok(()),table)''',
(r,'balance_qm31_rows'):'''if row<1024 {let after=balance_qm31_step(sum,table[row],active[row],row,dependent);
balance_qm31_rows(table,dependent,active,row+1,after)}else{sum}''',
(r,'balance_qm31_step'):'''if !active && row!=dependent {sum.add(value)} else {sum}'''}
for (p,f),body in list(expected.items()):
 expected[p,f.replace('qm31','m31')]=body.replace('aspis_core::field::QM31','M31').replace('QM31','M31').replace('qm31','m31')
checks=[]
for (p,f),body in expected.items():
 actual=take(p,f);assert norm(actual)==norm(body),(p,f)
 checks.append(dict(path=p,function=f,body_sha256=hashlib.sha256(actual.encode()).hexdigest()))
c=(R/'crates/aspis-statement/src/state_only_poseidon.rs').read_text()
assert re.search(r'pub const STATE_ONLY_POSEIDON_TRACE_ROWS:\s*usize\s*=\s*1\s*<<\s*10;',c)
diff=R/'tools/pv-l2c-20261028/differential/balance_cut.rs'
prior=json.loads((R/'evidence/pv-l2c-20261028/native-after-42695/receipt.json').read_text())
assert hashlib.sha256(diff.read_bytes()).hexdigest()==prior['source_sha256']['balance_cut.rs']
assert prior['exit']==0
out=dict(evidence_class='structural (K-1 substitute)',scope='M31 and QM31 balancing cuts only; length=1024, dependent<1024, dependent inactive; no honest sampler/caller association',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),checks=checks,
 differences=[
 dict(change='Borrowed slice vs owned Vec and Result/table pair',law='PV_L2C_VecRead.read; PV_L2C_VecBack.index_mut/write; PV_L2C_OwnedBalance.complete_result'),
 dict(change='While loop vs ascending tail recursion',law='R1Z.ProverCommitBalanceRecursion.qm31_all_rows/sequence_ascending; PV_L2C_RowEnumeration.enumeration; PV_L2C_SelectedDense.selected_sum'),
 dict(change='Reference eagerly reads table[row] before the active test; native reads it only on the addition arm',law='PV_L2C_VecRead.read and PV_L2C_ExtractedRows.read_step on rows<1024: pure successful reads, no output/state change; no observation-trace equivalence asserted'),
 dict(change='Dead rows local and intermediate value binding',law='No calls, state effects or error paths; let substitution'),
 dict(change='QM31 qualified name and trace-row constant',law='Same aspis_core field type, constant checked =1024')],
 complete_Result_law=['PV_L2C_OwnedBalance.complete_result','PV_L2C_ScalarBalance.complete_result'],guard_law='PV_L2C_ExtractedGuard.padding_result',
 finite_validation=dict(receipt='evidence/pv-l2c-20261028/native-after-42695/receipt.json',cases=128,changed_writes=128,classification='same-input native differential, finite validation; reused unchanged source cut'),
 limitations=['Does not bind native sampler randomness to this table','Does not bind HonestInput native caller geometry or guard consumer','Does not prove an observation-trace refinement','Does not subtract V352/V354/V357/V360'])
(E/'balance-structural.json').write_text(json.dumps(out,indent=2)+'\n');print('Checked twelve bodies and constant; retained finite differential; no whole-site closure')
