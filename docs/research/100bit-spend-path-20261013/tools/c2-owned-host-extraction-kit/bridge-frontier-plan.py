#!/usr/bin/env python3
"""Pin the smallest proposed actual-source bridge spans; no source changes."""
from pathlib import Path
import argparse,hashlib,json,subprocess
ROOT=Path(__file__).resolve().parents[5]
sha=lambda b:hashlib.sha256(b).hexdigest()
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--revision',required=True);ap.add_argument('--out',type=Path,required=True);ap.add_argument('--check',action='store_true');a=ap.parse_args()
 ref=subprocess.check_output(['git','-C',str(ROOT),'rev-parse',a.revision]).decode().strip()
 paths={'backend':'crates/aspis-r1-cost-probe/src/prover.rs','build':'crates/aspis-r1-cost-probe/src/host_commitment.rs'}
 files={n:subprocess.check_output(['git','-C',str(ROOT),'show',ref+':'+p]) for n,p in paths.items()}
 specs=[
 ('backend_copy_loop','backend',b'        for (i,c) in columns.into_iter().enumerate(){self.messages[26+i]=c.map(E::from_qm31);}',None),
 ('backend_salt_take_and_store','backend',b'        let c=if let Some(salts)=self.c2_salts.take()',b'    }\n}'),
 ('build_indices_match','build',b'        let indices: &[usize] = match time {',b'        let mut lanes = filled(indices.len(), 0)?;'),
 ('build_owned_lanes','build',b'        let mut lanes = filled(indices.len(), 0)?;',b'        let mut words = Vec::new();'),
 ('build_encode_and_retain_prefix','build',b'        let mut words = Vec::new();',b'        let mut leaves = filled(FIBRE_COUNT, [0; 32])?;'),
 ('build_pack_and_finish','build',b'        let mut leaves = filled(FIBRE_COUNT, [0; 32])?;',b'    pub fn root(&self) -> [u8; 32] {')]
 spans=[]
 for name,key,start,end in specs:
  raw=files[key];assert raw.count(start)==1,(name,'start');i=raw.index(start)
  if end is None:j=i+len(start)
  else:
   j=raw.index(end,i+len(start))
  b=raw[i:j];spans.append({'name':name,'path':paths[key],'file_sha256':sha(raw),'start_byte':i,'end_byte_exclusive':j,'start_line':raw[:i].count(b'\n')+1,'end_line_inclusive':raw[:j-1].count(b'\n')+1,'sha256':sha(b),'source':b.decode()})
 result={'classification':'READ_ONLY_SOURCE_SPAN_PROPOSAL_NOT_ADOPTED_NOT_1F_QUALIFIED','revision':ref,'spans':spans,
 'compiler_frontier':[
  {'case':'exact Backend::c2','archive':'evidence/c2-owned-host-20261017/checkpoint.tar.gz','log_member':'actual-caller/runs/aeneas-a/stdout.log','compiler':'symbolic/SymbolicToPureAbs.ml:1313','lib_span':'220:4-224:5','interpretation':'whole function end-abstraction failure; not proof that HashFn alone is the cause'},
  {'case':'exact Commitment::build','archive':'evidence/c2-owned-host-20261017/checkpoint.tar.gz','log_member':'actual-build/runs/aeneas-a/stdout.log','compiler':'interp/InterpJoin.ml:2209','lib_span':'308:32-313:43','source_span':'build_indices_match'},
  {'case':'copy helper relocation, still whole Backend root','archive':'evidence/c2-followup-diagnostics-20261017/followup-diagnostics.tar.gz','log_member':'copy-helper/runs/aeneas-a/stdout.log','compiler':'symbolic/SymbolicToPureAbs.ml:1313','lib_span':'221:4-225:5','interpretation':'does not test helper-only root acceptance; zero accepted helper cone'},
  {'case':'owned lane-allocation branches diagnostic','archive':'evidence/c2-followup-diagnostics-20261017/followup-diagnostics.tar.gz','log_member':'owned-lanes/runs/aeneas-a/stdout.log','compiler':'interp/InterpJoin.ml:1680','lib_span':'353:32-353:59','interpretation':'reaches later packing-width branch; no whole-function or prefix acceptance inferred'},
  {'case':'owned lanes plus opaque packing helper diagnostic','archive':'evidence/c2-followup-diagnostics-20261017/followup-diagnostics.tar.gz','log_member':'owned-prefix/runs/aeneas-a/stdout.log','compiler':'interp/InterpAbs.ml:191','lib_span':'1:0-355:5','interpretation':'still rejects whole function; not an accepted constructor prefix'}],
 'next_diagnostics':[
  {'priority':1,'target':'copy_c2_columns helper alone','source_span':'backend_copy_loop','transformation':'Move exact loop into private helper taking only &mut Vec<Message<E>> and owned [&[K;1024];2]; replace only self.messages with messages. Make the diagnostic entry call that helper, not Backend::c2. No unroll unless separately needed and qualified.','derived_fact_needed':'Actual successful helper output contains from_qm31(H1[r]) and from_qm31(G[r]) in lanes26/27, with other lanes and error mutation prefix preserved.','remaining_caller':'Actual Backend::c2 still must call this emitted helper and retain salt take/constructor map_err/root/c2 store order; helper-only acceptance does not prove caller execution.'},
  {'priority':2,'target':'encode_and_retain_lanes helper alone','source_span':'build_encode_and_retain_prefix','transformation':'Move exact words/saved allocations and loop into private helper taking &EncodingDomain, &[Message<E>], Variant, &[usize], returning owned (words,saved). Caller retains initial guards, actual lanes allocation/copy, then invokes helper, then original packing/tree block. No synthetic encoder result or replacement of variant.coefficients body.','derived_fact_needed':'For actual two-lane iteration and real helper success, returned Word::Secure vectors are the two actual domain.encode returns for projected actual variant.coefficients; saved rows are the input rows. Actual caller must derive lanes=[26,27] from its match/allocation/copy, rather than assume final custody.','remaining_caller':'Borrowed-index match, whole-build carrier/end-abstraction, packing/tree and Backend caller refinement remain separate until accepted caller emission. Existing owned-lanes diagnostic is evidence of compiler frontier only.'}],
 'preservation_requirements':['Keep all message/salt length checks before allocation.','Keep lanes allocation/copy before words reserve, saved reserve, and lane loop.','Keep each WrongField check before that lane coefficients/encode, words.push before saved.push, and H1 before G.','Keep allocation/encode errors, Vec bounds behavior, and destructor/private-salt order; audit helper return/moves explicitly.','Keep Backend copy mutations before c2_salts.take; preserve take on constructor error, map_err Public, and root/store only on success.','Do not change packing, private salts, hash calls, tree construction, transcript or checkpoint.'],
 'adoption_gate':'No patch is proposed for direct adoption here. First obtain valid LLBC and successful Aeneas helper emission under actual source-equivalent boundaries, pin body/signature/source mapping, and coordinate A/root before judging standing1f coverage. New native gates belong to A if a source change is adopted.',
 'proof_scope':'The fresh checked primitive closes only per-element Wide construction. Neither this plan nor conditional Core proves actual Backend/build ownership, full recorded experiment, literalMessage custody, packing/salt-path or checkpoint.'}
 b=(json.dumps(result,indent=2,sort_keys=True)+'\n').encode()
 if a.check:assert a.out.read_bytes()==b
 else:a.out.write_bytes(b)
 print(json.dumps({'check':a.check,'revision':ref,'spans':len(spans),'sha256':sha(b)}))
if __name__=='__main__':main()
