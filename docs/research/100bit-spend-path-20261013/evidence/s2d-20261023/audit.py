#!/usr/bin/env python3
"""Pinned lexical inventory and verbatim observer extraction; not Rust refinement."""
from pathlib import Path
import hashlib, json, re, subprocess, sys
base=Path(__file__).resolve().parent
root=next(p for p in base.parents if (p/'programs/r1-cost-probe/src/lib.rs').exists())
paths=['programs/r1-cost-probe/src/r1_pool_adapter.rs','programs/r1-cost-probe/src/lib.rs','crates/aspis-r1-cost-probe/src/verifier.rs','programs/r1-cost-probe/src/pool_route.rs']
sources={p:(root/p).read_text() for p in paths}
def function(text,name):
 m=re.search(r'(?m)^(?:pub(?:\(super\))? )?fn '+name+r'\b',text); assert m,name
 start=m.start(); b=text.index('{',m.end()); depth=1; end=b+1
 while depth:
  depth += (text[end]=='{')-(text[end]=='}'); end+=1
 return text[start:end],text[:start].count('\n')+1
rows=[]
# Lexical sites are exhaustive within these reachable adapter functions; child
# internals remain separately owned. No claim this is a control-flow proof.
names=['readonly_meta_ok','require_readonly_account','readonly_buffer_meta_ok','require_readonly_buffer','require_verifier_checkpoint','require_distinct_accounts','decode_public_statement_box','decode_master_box','decode_checkpoint_box','decode_lane_from_pool_release','authenticate_invariant_release_registry','authenticate_asq8_accounts','scan_proof_buffer','asq8_common','transfer_statement_box','withdrawal_statement_box','reconstruct_asq8_statement','validate_asq8','emit_result','stage1','stage2','process']
for name in names:
 body,line=function(sources[paths[0]],name)
 sites=[]
 for i,text in enumerate(body.splitlines()):
  kinds=[k for k,pattern in [('try','?'),('mapped_error','map_err'),('explicit_error','Err('),('infallible_allocation','Box::new'),('syscall','program::set_return_data'),('pda','Pubkey::create_program_address'),('clock','Clock::get')] if pattern in text]
  if kinds: sites.append(dict(line=line+i,text=text.strip(),kinds=kinds,question_marks=text.count('?')))
 rows.append(dict(function=name,line=line,sha256=hashlib.sha256(body.encode()).hexdigest(),sites=sites))
obs,obsline=function(sources[paths[1]],'observer')
phase=re.search(r'pub enum Phase \{[^\n]+',sources[paths[2]]).group()
alias=re.search(r'pub type Observer=[^\n]+',sources[paths[2]]).group()
assert alias=='pub type Observer=Option<fn(Phase)>;'
crate='// Generated verbatim by ../audit.py; release cfg only.\nmod verifier {\n'+phase+'\n'+alias+'\n}\nuse verifier::Phase;\n'+obs+'''
#[cfg(kani)]
mod S2D_checks {
    #[kani::proof]
    fn actual_release_observer_is_typed_none() {
        let result: Option<fn(super::Phase)> = super::observer();
        match result { None => (), Some(_) => panic!("release observer present") }
    }
}
'''
report=dict(schema='s2d-source-audit-v1',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),sources={p:dict(sha256=hashlib.sha256(s.encode()).hexdigest(),size=len(s.encode())) for p,s in sources.items()},observer=dict(line=obsline,source=obs,phase=phase,alias=alias),functions=rows,limitations=['Lexical inventory only; imported child internals and compiler cleanup need native binding.','Box::new can abort on OOM; no ProgramError return or normal Drop is guaranteed.','Clock, PDA hashing, digest, error logging and return-data effects survive rejection.'])
# Revision is informational; source bytes determine --check stability.
if '--check' in sys.argv:
 prior=json.loads((base/'source-audit.json').read_text()); prior.pop('source_revision'); report.pop('source_revision'); assert prior==report
 assert (base/'kani-spec/src/lib.rs').read_text()==crate
 print('source pins, reachable lexical inventory and verbatim observer extraction match')
else:
 (base/'source-audit.json').write_text(json.dumps(report,indent=2)+'\n')
 (base/'kani-spec/src/lib.rs').write_text(crate)
