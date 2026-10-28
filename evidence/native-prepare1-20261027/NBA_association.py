"""Read-only lexical association of factored fragments with frozen source.
This checks the stated transformations, not Rust semantics or whole closure.
"""
from pathlib import Path
import subprocess,re,json,hashlib
from NBA_harness import source
E=Path(__file__).resolve().parent
R='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
def frozen(p):return subprocess.check_output(['git','show',R+':'+p],text=True)
def body(s,marker):
 i=s.index('{',s.index(marker));n=1;j=i+1
 while n:
  n+=(s[j]=='{')-(s[j]=='}');j+=1
 return s[i+1:j-1]
def norm(s):return re.sub(r'\s+','',re.sub(r'//[^\n]*','',s))
paths=['crates/aspis-r1-cost-probe/src/'+n+'.rs' for n in ['candidate','verifier','sampler','transcript']]+['crates/aspis-core/src/r0_transcript.rs']
f={p:frozen(p) for p in paths};v=f[paths[1]];s=f[paths[2]];c=f[paths[4]];hv=source();hs=source('crates/aspis-r1-cost-probe/src/NBA_sampler.rs');hc=source('crates/aspis-core/src/NBA_query_core.rs')
checks=[]
def eq(name,original,target,transformation):
 ok=norm(original)==norm(target);checks.append(dict(name=name,exact_tokens=ok,transformation=transformation,frozen_fragment_sha256=hashlib.sha256(original.encode()).hexdigest(),factored_fragment_sha256=hashlib.sha256(target.encode()).hexdigest()));assert ok,name
new=body(v[v.index('impl Prepared {'):],'pub fn new')
suffix=new[new.index('*g=powers::<29>(gamma);'):]
eq('continuing suffix',suffix,body(hv,'fn NBA_tail').replace('Prepared{','Self{'),'Self renamed Prepared; parameters expose already bound locals')
eq('post-scratch suffix',suffix[suffix.index('let claim='):],body(hv,'fn NBA_after_scratch').replace('Prepared{','Self{'),'Self renamed Prepared; parameters expose already bound locals')
eq('scratch overwrite','*g=powers::<29>(gamma);',body(hv,'fn NBA_write'),'statement isolated without alteration')
word=body(body(c,'fn scan('),'for candidate in query_words(block)')
word=word.replace('self.accepted[..self.accepted_len].contains(&candidate)','member');word=re.sub(r'\bself\b','s',word)+'false'
eq('query word iteration',word,body(hc,'fn NBA_word_step'),'self renamed s; pure contains replaced by unrestricted Bool; false continuation marker appended')
add=body(body(s,'fn add_small_base_p'),'for digit in digits');add=re.sub(r'\baddend\b','*addend',add)
eq('carry digit iteration',add,body(hs,'fn NBA_add_digit'),'owned mutable addend represented by mutable-reference parameter')
div=body(body(s,'fn qm31_div_pass'),'while j > 0');div=re.sub(r'\bremainder\b','*remainder',div);div=re.sub(r'\bj\b','*j',div)
eq('rho descending division iteration',div,body(hs,'fn NBA_qdiv_iteration'),'owned mutable remainder and j represented by mutable-reference parameters')
digit=body(body(s,'fn qm31_digits'),'while i < 4');digit=digit.replace('qm31_div_pass(rank)','qm31_div_pass(*rank)');digit=re.sub(r'\brank\s*=','*rank=',digit);digit=re.sub(r'\bi\b','*i',digit)
eq('rho outer digit iteration',digit,body(hs,'fn NBA_qdigits_iteration'),'owned mutable rank/i represented by mutable references; same array stores and callee')
# Identity of the typed record after exposing bound expressions as arguments.
initializer='Self{variant:v.variant,roots:sem.roots,gamma,kappa,alpha,rho,queries,semantic_alpha:sem.alpha,z:sem.z,claim,state:t.state}'
assert norm(initializer) in norm(new)
record=body(hv,'fn NBA_record(')
normalized=initializer.replace('Self{','Prepared{').replace('variant:v.variant','variant').replace('roots:sem.roots','roots').replace('semantic_alpha:sem.alpha','semantic_alpha').replace('z:sem.z','z').replace('state:t.state','state')
assert norm('Box::new('+normalized+')') in norm(record)
checks.append(dict(name='typed Prepared initializer',exact_tokens=True,transformation='Self renamed Prepared; each source field expression exposed as SAME routed typed argument',frozen_expression=initializer))
current={p:hashlib.sha256(Path(p).read_bytes()).hexdigest() for p in paths}
pins={p:hashlib.sha256(t.encode()).hexdigest() for p,t in f.items()};assert current==pins
out=dict(frozen_revision=R,source_sha256=pins,repository_source_unchanged=True,checks=checks,scope='Lexical factored-fragment association only. Actual method gates are identified separately; no full native prepare theorem inferred.')
(E/'NBA_ASSOCIATION.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(dict(checks=len(checks),all_exact=True)))
