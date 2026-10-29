"""Read-only frozen source spans and ordered source-stage checks, not a proof of refinement."""
from pathlib import Path
import hashlib,json,subprocess
R=Path(__file__).resolve().parents[2]; E=R/'evidence/pv-ownj-20261029'
spans=[('claims','crates/aspis-prover/src/state_only_candidate_prefix.rs',749,760),('construction','crates/aspis-prover/src/state_only_candidate_prefix.rs',785,895),('queries','crates/aspis-prover/src/state_only_hiding.rs',1587,1628),('transcript','crates/aspis-core/src/state_only_prefix.rs',1722,1759),('points','crates/aspis-core/src/state_only_prefix.rs',600,613)]
rows=[]
for name,path,start,end in spans:
 b=(R/path).read_bytes();text=''.join(b.decode().splitlines(True)[start-1:end])
 rows.append(dict(name=name,path=path,first_line=start,last_line=end,file_sha256=hashlib.sha256(b).hexdigest(),span_sha256=hashlib.sha256(text.encode()).hexdigest(),text=text))
checks={
 'claims':['wire::statement_points(point)','columns.iter().enumerate()','multilinear_evaluate_qm31(column, at).ok_or(Error::Public)?'],
 'construction':['v.len() != 1024','let h1 = helper(lambda, chi)?','h1.as_slice().try_into()','let columns: [Vec<QM31>; 29]','26 => h1.to_vec()','27 => g.to_vec()','_ => d.to_vec()','prove_sumcheck(','point_claims(&columns, point)?','point_claims(&columns, &alpha)?'],
 'queries':['let mut point = [QM31::ZERO; 10]','for round in 0..10','for (sample, value)','point[round] = QM31::from_cm31','for assignment','point[round + 1 + offset]','oracle(&point)?','let polynomial = interpolate','wire::record(','point[round] = transcript.semantic','output.extend_from_slice(&framed)','if oracle(&point)?','Ok((point, running))'],
 'transcript':['state: hash(&[DOMAIN','fn sample_block','parse_record(row, framed)?','let absorbed =','let block =','self.state =','self.next_row += 1','Ok(block)','pub fn semantic','qm31_sample'],
 'points':['let mut successor = *z','let mut carry = QM31::ONE','for coordinate in (0..z.len()).rev()','let bit_and_carry = bit.mul(carry)','successor[coordinate] =','carry = bit_and_carry','let mut absorption = *z','absorption[7]','absorption[6]','[*z, successor, absorption]']}
for row in rows:
 pos=-1
 for token in checks[row['name']]:
  pos=row['text'].index(token,pos+1)
 row['ordered_tokens']=checks[row['name']]
(E/'source-binding.json').write_text(json.dumps(dict(revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),classification='partial structural source-stage binding under own-1; concrete decoder/owned consumer refinement not supplied',rows=rows),indent=2)+'\n')
print('Pinned and checked ordered stages for',len(rows),'source spans; no compiler invocation')
