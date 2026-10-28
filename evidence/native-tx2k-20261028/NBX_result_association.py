from pathlib import Path
import subprocess,re,json,hashlib
E=Path(__file__).resolve().parent;rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
p='crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs'
frozen=subprocess.check_output(['git','show',rev+':'+p],text=True)
cut=Path('evidence/native-tx2j-20261028/NBU_more.rs.txt').read_text()
def body(s,n):
 m=re.search(r'\bfn '+n+r'\b',s);assert m,n
 start=s.index('{',m.end());i=start+1;depth=1
 while depth:depth+=(s[i]=='{')-(s[i]=='}');i+=1
 return s[start:i]
a=body(frozen,'validate_result');b=body(cut,'NBU_result_cut')
subs={'pool_v1_pair_forest_output_lane_v1':'lane','encode_pool_v1_pair_verified_afterstate_v1':'after'}
n=a
for x,y in subs.items():n=re.sub(r'\b'+x+r'\b',y,n)
normalize=lambda s:re.sub(r'\s+','',s)
assert normalize(n)==normalize(b),'STOP result cut differs beyond two named child call substitutions'
x=dict(revision=rev,path=p,native_body=a,cut_body=b,substitutions=subs,normalized_body_equal=True,native_source_sha256=hashlib.sha256(frozen.encode()).hexdigest(),cut_source_sha256=hashlib.sha256(cut.encode()).hexdigest(),claim='exact source body under two named closed-callee substitutions; no adapter law or successful-child premise')
(E/'NBX_RESULT_ASSOCIATION.json').write_text(json.dumps(x,indent=2)+'\n');print('exact result cut association checked')
