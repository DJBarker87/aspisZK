"""Frozen source-fission association; syntax evidence, never a semantic verdict."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
E=Path(__file__).resolve().parent;rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
def braced(s,start):
 i=s.index('{',start);j=i+1;depth=1
 while depth:depth+=(s[j]=='{')-(s[j]=='}');j+=1
 return s[i+1:j-1],j

def tokens(s):return re.findall(r'[A-Za-z_][A-Za-z_0-9]*|[0-9]+|[^\s]',re.sub(r'//[^\n]*','',s))
frozen=subprocess.check_output(['git','show',rev+':crates/aspis-r1-cost-probe/src/multiproof.rs'],text=True)
h=(E/'NJP_multiproof.rs').read_text();b,_=braced(frozen,frozen.index('while i < n',frozen.index('pub fn verify_in_place')))
binary,_=braced(b,b.index('Arity::Two =>'));at=b.index('match arity');_,end=braced(b,at);b=b[:at]+binary.strip()+b[end:]
b=b.replace('arity.bits()','Arity::Two.bits()').replace('occupied_binary_parent(hash,','NJP_row_occupied(log,').replace('sibling_binary_parent(hash,','NJP_row_sibling(log,')
actual,_=braced(h,h.index('if *i<n',h.index('fn NJP_binary_row(')))
actual=actual.replace('if cfg!(NJP_write_stage){NJP_digest_write_record(log,val,*w,digest);}else{val[*w]=digest;}','val[*w]=digest;')
actual=actual.replace('super::','');actual=re.sub(r'\*(i|w|at)\b',r'\1',actual)
assert tokens(b)==tokens(actual),'unexpected binary source transformation'
# One corrupted parent argument must not survive the source-association check.
mutation=actual.replace('NJP_row_occupied(log,val,i)','NJP_row_occupied(log,val,i+1)',1)
assert tokens(b)!=tokens(mutation)
poseidon=subprocess.check_output(['git','show',rev+':crates/aspis-statement/src/poseidon2.rs'],text=True)
p=(E/'NJP_poseidon.rs').read_text()
source=poseidon[poseidon.index('pub fn permute_optimized_with_trace<F>'):poseidon.index('\n/// Domain-separated',poseidon.index('pub fn permute_optimized_with_trace<F>'))]
transformed=p[p.index('fn NJP_controller<F>'):p.index('\nfn NJP_controller_case')]
transformed=transformed.replace('fn NJP_controller<F>(state: &mut [M31; 16], mut trace: F, log: &mut NJP_Control)','pub fn permute_optimized_with_trace<F>(state: &mut [M31; 16], mut trace: F)')
transformed=transformed.replace('NJP_linear_control(log, 0);','external_linear_lazy(state);').replace('NJP_linear_control(log, 1);','internal_linear_lazy(state);')
transformed=transformed.replace('NJP_cell_control(log, index, constants[index]);','state[index] = pow5(state[index].add(M31(constants[index])));').replace('NJP_cell_control(log, 0, constant);','state[0] = pow5(state[0].add(M31(constant)));')
transformed=transformed.replace('NJP_callback(log, &mut trace, Poseidon2RoundTransition {','trace(Poseidon2RoundTransition {')
assert tokens(source)==tokens(transformed),'unexpected controller transformation'
assert tokens(source)!=tokens(transformed.replace('ExternalInitial(index as u8)','ExternalFinal(index as u8)',1))
comp_source,_=braced(poseidon,poseidon.index('pub fn merkle_node_compress_v3('));comp_native,_=braced(p,p.index('fn NJP_compress('))
assert tokens(comp_source)==tokens(comp_native.replace('NJP_permutation(log, &mut state);','permute_optimized_with_trace(&mut state, |_| {});'))
result=dict(frozen_revision=rev,binary_token_erasure=True,controller_token_erasure=True,compression_token_erasure=True,mutation_tests=2,whole_buffer_loop=False,source_sha256={'multiproof':hashlib.sha256(frozen.encode()).hexdigest(),'poseidon2':hashlib.sha256(poseidon.encode()).hexdigest()},harness_sha256={'multiproof':hashlib.sha256(h.encode()).hexdigest(),'poseidon2':hashlib.sha256(p.encode()).hexdigest()},substitutions=['binary-only one iteration, exact SAME-input parent logs','digest assignment staged as local write record; complete native real write-window gate required','controller arithmetic bodies are control-only records; enum construction/callback/ranges retained','compression permutation boundary only; all seed/copy/output source operations retained'],native_credit=False)
(E/'NJP_SOURCE_ASSOCIATION.json').write_text(json.dumps(result,indent=2)+'\n')
print('NJP source fission: three exact frozen skeletons; two mutations rejected; no semantic credit inferred')
