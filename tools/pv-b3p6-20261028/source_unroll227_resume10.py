"""Fail-closed exact-token checks for nine loop-only source rewrites.
No interpretation of a token diff as an exhaustive callback binding.
"""
from pathlib import Path
import re,json,hashlib,sys
P=Path('tools/pv-b3p6-20261028/v244');O=Path('evidence/pv-b3p6-20261028/resume10')
lex=re.compile(r'//[^\n]*|/\*[\s\S]*?\*/|"(?:\\.|[^"\\])*"|\w+|[^\s]')
def toks(s):return [re.sub(r'^(\d+)usize$',r'\1',m[0])for m in lex.finditer(s)if not m[0].startswith(('//','/*'))]
def extract(s,name):
 a=s.index('fn '+name+'(');k=s.index('{',a);j=k+1;depth=1
 while depth:depth+=(s[j]=='{')-(s[j]=='}');j+=1
 return s[a:j]
rows=[]
for name,bound,N,family in [('full_round','POSEIDON2_WIDTH',16,'poseidon'),('full_round_packed','POSEIDON2_WIDTH',16,'poseidon'),('full_round_m31_constants','POSEIDON2_WIDTH',16,'poseidon'),('full_round_m31_constants_packed','POSEIDON2_WIDTH',16,'poseidon'),('leading_pair','RATE',8,'poseidon'),('leading_pair_packed','RATE',8,'poseidon'),('path_lanes_literal','DIGEST_ELEMS',8,'terminal'),('occupancy_lanes_literal','DIGEST_ELEMS',8,'terminal'),('occupancy_lanes_factored','DIGEST_ELEMS',8,'terminal')]:
 sf=Path('crates/aspis-statement/src/state_only_poseidon.rs')if family=='poseidon'else P/'host_terminal.rs';rf=P/('reference_'+family+'.rs');source=extract(sf.read_text(),name);owned=extract(rf.read_text(),name)
 match=re.search(r'for lane in 0\s*\.\.\s*'+bound+r'\s*\{',source);assert match,name
 k=match.end();j=k;depth=1
 while depth:depth+=(source[j]=='{')-(source[j]=='}');j+=1
 inner=source[k:j-1];expanded='\n'.join(re.sub(r'\blane\b',str(i)+'usize',inner)for i in range(N));expected=source[:match.start()]+expanded+source[j:]
 # These dead scalar declarations remain in two historical owned unrolls.
 norm=re.sub(r'let mut lane_index = 0usize\s*;','',owned)
 assert toks(expected)==toks(norm),name
 theorem='PV_B3P_Binding10227.'+name+'_body_binding10'if name.startswith('full_round')else None
 rows.append(dict(body=name,source=str(sf),owned=str(rf),source_body_sha256=hashlib.sha256(source.encode()).hexdigest(),owned_body_sha256=hashlib.sha256(owned.encode()).hexdigest(),iteration_order=list(range(N)),step_source=inner.strip(),structural_check='exact complete-function token identity after fixed ordered loop expansion and dead scalar-local removal only',named_emitted_body_binding=theorem,remaining='std/dependency source binding; array-caller bounds; and named emitted binding where null'))
record=dict(rows=rows,classification='structural; fixed loop expansion checks, not exhaustive callback source binding',semantic_use='reclassification within existing Charon/Aeneas tool trust',compiler_boundary='V370 / pending owner D381,D386 retained',native_differential='existing64/36; finite validation only; unchanged')
p=O/'source-unroll-checks.json'
if '--check'in sys.argv:assert json.loads(p.read_text())==record
else:p.write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(dict(complete_function_token_checks=len(rows))))
