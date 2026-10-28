"""Check native guard/value-cut composition without granting a whole caller link."""
from pathlib import Path
import json,re,hashlib,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-l2c-20261028/resume-d371'
def compact(s):return re.sub(r'\s+','',re.sub(r'//[^\n]*','',s))
def body(s,marker):
 a=s.index(marker);a=s.index('{',a);b=a+1;depth=1
 while depth:
  depth+=(s[b]=='{')-(s[b]=='}');b+=1
 return s[a+1:b-1]
sem=(R/'crates/aspis-r1-cost-probe/src/host_semantic.rs').read_text()
hide=(R/'crates/aspis-prover/src/state_only_hiding.rs').read_text()
entropy=(R/'crates/aspis-prover/src/state_only_entropy.rs').read_text()
core=(R/'crates/aspis-core/src/field.rs').read_text()
probe=(R/'tools/pv-l2c-20261028/route-probe/guard_cut.rs').read_text()
checks={}
def check(source,marker,expected):
 b=body(source,marker);assert compact(b)==compact(expected),marker
 checks[marker]=hashlib.sha256(b.encode()).hexdigest()
check(sem,'fn check_semantic_columns(', 'check_base_columns(c1)?;check_secure_column(d)?;check_secure_column(g)')
check(sem,'fn check_base_columns(', 'let mut lane=0;while lane<26 {check_base_column(&c1[lane])?;lane+=1;}Ok(())')
check(sem,'fn check_base_column(',body(probe,'fn check_base_column('))
check(sem,'fn check_secure_column(','''let mut row=0;while row<1024 {let mut b=[0;16];column[row].write_le_bytes(&mut b);if QM31::from_le_bytes(&b).is_none(){return Err(Error::Public);}row+=1;}Ok(())''')
check(sem,'fn clone_semantic_columns(','''let mut c1:[Vec<M31>;26]=Default::default();let mut i=0;while i<16 {c1[i]=noised[i].clone();i+=1;}while i<26 {c1[i]=mask_only[i-16].clone();i+=1;}c1''')
check(hide,'fn m31(&mut self)', '''let limit=MASK_SAMPLE_RETRY_LIMIT;let mut retry=0;while retry<limit {let candidate=self.next_word()&0x7fff_ffff;if candidate<P{return Ok(M31(candidate));}retry+=1;}Err(StateOnlyMaskBuildError::MaskSampleExhausted)''')
assert 'const MASK_SAMPLE_RETRY_LIMIT: usize = 16;' in hide
check(entropy,'fn m31(&mut self)', '''let mut retry=0;while retry<16 {let candidate=self.next_word()&0x7fff_ffff;if candidate<aspis_core::field::P{return Ok(aspis_core::field::M31(candidate));}retry+=1;}Err(StateOnlyMaskBuildError::MaskSampleExhausted)''')
check(hide,'fn qm31(&mut self)', 'Ok(QM31{c0:CM31::new(self.m31()?,self.m31()?),c1:CM31::new(self.m31()?,self.m31()?),})')
check(hide,'fn sample_mask_cells(', 'let mut values=Vec::with_capacity(count);let mut i=0;while i<count {let value=expander.m31()?;values.push(value);i+=1;}Ok(values)')
check(hide,'fn apply_mask_cells(','''let mut i=0;while i<cells.len(){let row=usize::from(cells[i].row);let column=usize::from(cells[i].column);columns[column][row]=columns[column][row].add(masks[i]);i+=1;}''')
check(hide,'fn balance_m31_copy_inactive(','''let rows=STATE_ONLY_POSEIDON_TRACE_ROWS;if table.len()!=STATE_ONLY_POSEIDON_TRACE_ROWS||active[dependent]{return Err(StateOnlyMaskBuildError::TraceShape);}let sum=sum_m31_copy_inactive(table,dependent,active);let value=M31::ZERO.sub(sum);table[dependent]=value;Ok(())''')
check(hide,'fn sample_mask_g(','''let rows=STATE_ONLY_POSEIDON_TRACE_ROWS;let mut values=Vec::with_capacity(STATE_ONLY_POSEIDON_TRACE_ROWS);let mut row=0;while row<rows {let value=expander.qm31()?;values.push(value);row+=1;}balance_qm31_copy_inactive(&mut values,inactive,active)?;Ok(values)''')
check(entropy,'fn sample_source_d(','''let rows=STATE_ONLY_POSEIDON_TRACE_ROWS;let mut d=SensitiveQm31Vec(Vec::with_capacity(rows));let mut row=0;while row<rows{let value=expander.qm31()?;d.0.push(value);row+=1;}Ok(d)''')
check(entropy,'fn balance_source_d(','''let dependent=source_dependent_row(active)?;let sum=source_inactive_sum(d,active,dependent);let value=aspis_core::field::QM31::ZERO.sub(sum);d[dependent]=value;Ok(())''')
receipt=E/'route-probe2/receipt.json';r=json.loads(receipt.read_text());assert r['exit']==0
log=(E/'route-probe2/out.log').read_text();assert 'withdrawal=false account_decode=Ok full_compiler=Ok raw_C1_canonical=16 masked_base_canonical=26 native_inactive_balanced=26 full_prover=Ok(())' in log
assert 'withdrawal=true account_decode=Ok full_compiler=Ok raw_C1_canonical=16 masked_base_canonical=26 native_inactive_balanced=26 full_prover=Ok(())' in log
out={'revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),
 'evidence_class':'script-checked native value-cut bindings plus complete-Result owned laws and finite native validation; whole material/caller structural composition remains P',
 'exact_native_body_sha256':checks,'native_differential':{'receipt':str(receipt.relative_to(R)),'sha256':hashlib.sha256(receipt.read_bytes()).hexdigest(),'label':'finite validation: two generated-field canonical cases through native compiler, material application, all 26 base guards and actual prover; not exact planner reconstruction'},
 'laws':['PV_L2C_StateSampler.canonical_result','PV_L2C_StateSampler.secure_result','PV_L2C_SamplerFill.returned','PV_L2C_SampledBase.returned','PV_L2C_SampledMaskOnly.guard','PV_L2C_SampledSecure.guard','PV_L2C_N3Guard.expected','PV_L2C_MaterialN3.transfer','PV_L2C_MaterialN3.withdrawal'],
 'differences':[
 'Native up-counter retry<16 is owned remaining-fuel recursion; both call next_word once per rejected/accepted candidate and retain the post-call state. Universal stateful sampler/fill laws are proved, but the full native expander-state installation is not claimed here.',
 'QM31 is represented by four raw words in c0.a,c0.b,c1.a,c1.b order; parser law retains all four decodes and failures.',
 'Native dynamic vectors become bounded tables only after a successful length-preserving fill; reference fill proves exact returned length and all returned values.',
 'Native indexed mask writes become sequential functional updates on Fin-bounded cells; put/application prove every untouched and changed raw value remains canonical.',
 'Native base/secure error names map to publicError at the owned guard cut; the same base,d,g order and every first-error arm remain.',
 'Allocation/drop, panic on malformed layout and entire owned-material state/return association are not identified by these value lemmas; no observation coupling or endpoint premise removal follows.'],
 'remaining':['Instantiate MaterialN3.Executions from the entire native reserve/build/apply/derive/clone caller, including matching layout indexes and all returned states.',
 'Establish the exact selected-planner request/source domain inclusion, beyond the reviewed/generated/decoded field cuts.',
 'N2/N4 whole native sampler/geometry association; N5 native helper and QM31 inverse/norm association; N6 actual oracle/interpolation/running-claim association; E1/E2 and observation transport.'],
 'Kani':'none; no copy-dependent or Option<fn> PASS used'}
(E/'guard-source-check.json').write_text(json.dumps(out,indent=2)+'\n')
print('Checked',len(checks),'native value-cut bodies and both finite native prover outcomes; retained full-caller residual explicitly')
