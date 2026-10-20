#!/usr/bin/env python3
"""Pin the explicit resume source-fission and standard-array interpretation boundary."""
from pathlib import Path
import subprocess,sys,json,hashlib,argparse
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args()
tool=Path(__file__).resolve().parent;area=tool.parents[1];repo=tool.parents[4];sha=lambda b:hashlib.sha256(b).hexdigest()
for script in ['extract-retained-resume-fields.py','emit-retained-resume-source.py']:
 subprocess.run([sys.executable,str(tool/script),'--check'],check=True,stdout=subprocess.DEVNULL)
s=(tool/'rho-resume-caller-input/fragments/original-resume.rs').read_bytes()
for r in ['f458169f705f25b04e1e29546c621e4665e0f64c','39c2971dd16c95858a4cfd2c9ae35da052eacfa9']:
 assert s in subprocess.check_output(['git','-C',str(repo),'show',r+':crates/aspis-r1-cost-probe/src/verifier.rs'])
start=s.index(b'{')+1;e=s.index(b'let gamma=r.e()?;');rho=s.index(b'let rho=r.k()?;');query=rho+len(b'let rho=r.k()?;');sem=s.index(b'let mut semantic_alpha=[K::ZERO;10];');tail=s.index(b'    let z=',sem);power=s.index(b'let power=r.k()?;');endpower=power+len(b'let power=r.k()?;')
parts={'header_auth_state_roots':s[start:e],'actual_e4_decoder_calls':s[e:rho],'rho':s[rho:query],'queries_checks':s[query:sem],'semantic_array10_fill':s[sem:tail],'point_claim_rhs':s[tail:power],'power':s[power:endpower],'allocation_weights_tail':s[endpower:]}
assert b''.join(parts.values())==s[start:]
assert b'let gamma=r.e()?;let kappa=r.e()?;let alpha=[r.e()?,r.e()?];' in parts['actual_e4_decoder_calls']
assert parts['semantic_array10_fill'].strip()==b'let mut semantic_alpha=[K::ZERO;10];for x in &mut semantic_alpha {*x=r.k()?;}'
for n in ['header_auth_state_roots','queries_checks','point_claim_rhs']:
 assert b'semantic_alpha'not in parts[n] and b'alpha['not in parts[n]
assert s.count(b'semantic_alpha')==3 # declaration, iterator target, immutable final constructor shorthand
output=dict(original_resume_sha256=sha(s),original_revisions=['f458169f705f25b04e1e29546c621e4665e0f64c','39c2971dd16c95858a4cfd2c9ae35da052eacfa9'],complete_fragment_reassembly=True,fragments={n:dict(sha256=sha(b),source=b.decode()) for n,b in parts.items()},selected_direct_extraction_roots=['crate::begin_fields'],array_loop_direct_aeneas_checked=False,array_frontend_failure='InterpReduceCollapse.ml1137, receipts retained-resume-fields-aeneas-{a,b,c,d,e,f,g}; never admitted as successful extraction',explicit_source_interpretation='CuSavingsRetainedResumeCells.cells n executes ordered actual source_read_k calls, exits immediately with same first runtime failure/divergence/Rust error, constructs the length-indexed result via one cons per successful read. n=10 instantiates the source fixed MutArray full-overwrite loop. Standard owning-array/iterator handback admission: each successful iteration writes its unique next cell, no alias/escape/observer of initial zeros, error exit does not return local array. This narrow source interpretation is an explicit boundary, not claimed direct full-loop Aeneas emission.',retained_source_bindings=['actual CanonicalReader.Reader.e plus coordinate-only transport','actual source_read_k -> existing AspisR1CuRho.verifier.Reader.k with exact parser/raw source','original complete RhoResumeCaller constructs returned Prepared/Accumulator with exact retained fields'],common_fragments='Only exact header/auth/state/roots, queries/checks and point/claim/rhs source computations remain opaque computational fields; no proposition/canonicality/equivalence law. They cannot receive or overwrite stored alpha/gamma/semantic_alpha.')
p=tool/'retained-resume-source-admission.json';text=json.dumps(output,indent=2)+'\n'
if a.check:assert p.read_text()==text
else:p.write_text(text)
print(json.dumps(dict(check=a.check,original=sha(s),direct_begin_only=True,explicit_array_source_boundary=True)))
