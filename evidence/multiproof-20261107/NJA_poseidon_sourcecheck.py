from pathlib import Path
import hashlib,json,re,subprocess
E=Path(__file__).parent
revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
raw=subprocess.check_output(['git','show',revision+':crates/aspis-statement/src/poseidon2.rs'],text=True)
log=(E/'NJA_poseidon.rs').read_text()
def body(s,name):
 m=re.search(r'fn '+re.escape(name)+r'\s*\(',s);assert m
 i=s.index('{',m.end());n=1;j=i+1
 while n:
  n+=(s[j]=='{')-(s[j]=='}');j+=1
 return s[i+1:j-1]
def tokens(s):return re.sub(r'\s+','',s)
a=body(raw,'apply_mat4_lazy');b=body(log,'NJA_mat4').replace('NJA_reduce(log,','M31::reduce_u62(')
assert tokens(a)==tokens(b)
p=body(raw,'pow5');q=body(log,'NJA_pow5')
assert tokens(p)=='letsquare=value.mul(value);square.mul(square).mul(value)'
assert tokens(q)=='letsquare=NJA_product(log,value,value);letfourth=NJA_product(log,square,square);NJA_product(log,fourth,value)'
x=dict(frozen_revision=revision,source_sha256=hashlib.sha256(raw.encode()).hexdigest(),log_sha256=hashlib.sha256(log.encode()).hexdigest(),mat4_token_erasure=True,pow5_anf_association=True,pow5_rule='evaluate receiver square.mul(square), then outer .mul(value); arguments and order unchanged; product replacements are local log calls',native_credit=False,remaining='Instantiate paired Lean laws on same logged arguments and prove adopted M31 carrier/trace association; no automatic closure from syntactic check')
(E/'NJA_POSEIDON_SOURCE.json').write_text(json.dumps(x,indent=2)+'\n');print('NJA source association: matrix token erasure and pow5 three-call ANF checked; no closure credit')
