#!/usr/bin/env python3
"""Read-only freeze/call-site audit; source observations are not refinements."""
from pathlib import Path
import hashlib,json,subprocess
R=Path(__file__).resolve().parents[2]; E=R/'docs/research/100bit-spend-path-20261013/evidence/s2-kani-20261021'
paths=['programs/r1-cost-probe/src/lib.rs','programs/r1-cost-probe/src/r1_pool_adapter.rs','crates/aspis-r1-cost-probe/src/'+ 'candidate.rs','crates/aspis-r1-cost-probe/src/verifier.rs','crates/aspis-r1-cost-probe/src/r1_wire.rs','crates/aspis-r1-cost-probe/src/r1_semantic.rs','crates/aspis-r1-cost-probe/src/transcript.rs']
def canon(s):return ''.join(s.split())
def item(s,marker):
 a=s.index(marker);b=s.index('{',a);d=1;e=b+1
 while d:d+=(s[e]=='{')-(s[e]=='}');e+=1
 return s[a:e]
s={p:(R/p).read_text() for p in paths}
for p in paths:assert subprocess.check_output(['git','show','b2727acd3:'+p])==(R/p).read_bytes(),p
p,a,c,v,w,sem,t=[s[x] for x in paths]
checks={
 'stage1_first_decoded':(a,'let checkpoint = super::first_decoded(statement.semantic_public(), &public_data, &proof_data[proof_start..proof_end], data[1] as usize)?;'),
 'stage1_accounts':(a,'let proof_account = &accounts[0];\nlet public_account = &accounts[1];\nlet checkpoint_account = &accounts[2];'),
 'stage1_range':(a,'let proof_length = verifier::PROOF_BYTES;\nlet proof_start = POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES;\nlet proof_end = proof_start.checked_add(proof_length)\n.ok_or(ProgramError::InvalidAccountData)?;'),
 'stage2_call':(a,'verifier::tx2_authenticated(\n&public_bytes,\n&proof_data[proof_start..proof_end],\n&checkpoint_data,\nsuper::SolanaDigest,\nsuper::observer(),\n)\n.map_err(super::error)?;'),
 'stage2_reconstruction':(a,'let public_bytes = encode_pool_v1_pair_forest_terminal_statement_v1(&validated.statement)\n.map_err(|_| ProgramError::InvalidInstructionData)?;'),
 'first':(p,'first_decoded(statement.semantic_public(),public_bytes,proof,k)'),
 'observer_off':(p,'#[cfg(not(feature="cu-profiling"))] {None}'),
 'prepare_expand':(c,'compact::expand_semantic(&proof[compact::OFF_SEMANTIC..compact::OFF_Y1], semantic)?;\ncompact::expand_values(&proof[compact::OFF_Y1..compact::OFF_INACTIVE], y1)?;'),
 'prepare_semantic':(c,'let sem = crate::r1_semantic::verify_observed(public, v.semantic, hash, obs).map_err(|_| Error::Semantic)?;'),
 'circle25':(sem,'let z0 = transcript.circle_validated(prefix.validated_record(25)?)?;'),
 'circle26':(sem,'let z1 = transcript.circle_validated(prefix.validated_record(26)?)?;'),
 'row27':(v,'let gamma=t.scalar(27,v.y1,true);'),
 'row28':(v,'let kappa=t.scalar(28,&v.inactive.to_le_bytes(),false);'),
 'row29':(v,'let alpha0=t.scalar(29,v.round0,false);'),
 'row30':(v,'let mut bytes=Vec::with_capacity(32+224);bytes.extend_from_slice(v.folded_root.unwrap());bytes.extend_from_slice(v.round1);'),
 'row31_32':(v,'let queries=t.queries(row,v.final_message)?;\nlet rho=t.scalar_k(row+1,&[]);'),
}
for name,(source,fragment) in checks.items():assert canon(fragment) in canon(source),name
schedules={}
for name in ['tx1','tx2','tx2_authenticated']:
 body=item(c,'pub fn '+name+'<')
 schedules[name]=body
 assert body.index('parse_shape(proof)?') < body.index('mark(obs, Phase::Parsed)')
assert schedules['tx1'].index('if k != SPLIT') < schedules['tx1'].index('parse_shape(proof)?')
endpoints={}
for name in ['R1FinalSoundnessHeadline','R1FinalSoundnessBinPerQueryR19']:
 path='docs/research/100bit-spend-path-20261013/lean/'+name+'.lean'
 before=subprocess.check_output(['git','show','5b6193eec:'+path]);after=(R/path).read_bytes();assert before==after
 endpoints[name]=hashlib.sha256(after).hexdigest()
result=dict(schema='s2-source-ledger-v1',revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),freeze='b2727acd3',sources={p:hashlib.sha256((R/p).read_bytes()).hexdigest() for p in paths},fragments={k:v[1] for k,v in checks.items()},verifier_bodies=schedules,unchanged_headlines=endpoints,qualification='Exact source identities, guards and order, not a theorem about AccountInfo/runtime/backend/model interpretation.')
(E/'source-ledger.json').write_text(json.dumps(result,indent=2)+'\n')
