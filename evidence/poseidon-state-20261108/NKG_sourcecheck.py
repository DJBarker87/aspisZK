from pathlib import Path
import subprocess,re,json,hashlib
E=Path(__file__).resolve().parent
s=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:crates/aspis-statement/src/state_only_poseidon.rs'],text=True)
h=(E/'NKG_state_native.rs').read_text()
def body(s,at):
 i=s.index('{',at);j=i+1;d=1
 while d:d+=(s[j]=='{')-(s[j]=='}');j+=1
 return s[i+1:j-1]
def tokens(s):return re.findall(r'[A-Za-z_][A-Za-z_0-9]*|[0-9]+|[^\s]',re.sub(r'//[^\n]*','',s))
b=body(s,s.index('while lane < POSEIDON2_WIDTH',s.index('fn interpolate_three_constant_columns(')))
expected=b.replace('interpolate_three_constant_limb(','NKG_limb(log,').replace('lane += 1;','*lane += 1;').replace('[lane]','[*lane]')
actual=body(h,h.index('if *lane<POSEIDON2_WIDTH'))
assert tokens(expected)==tokens(actual),'source-iteration erasure mismatch'
assert tokens(expected)!=tokens(actual.replace('column0[*lane]','column1[*lane]',1))
x=dict(frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',source_sha256=hashlib.sha256(s.encode()).hexdigest(),harness_sha256=hashlib.sha256(h.encode()).hexdigest(),column_iteration_exact_token_erasure=True,argument_mutation_rejected=True)
(E/'NKG_SOURCE_ASSOCIATION.json').write_text(json.dumps(x,indent=2)+'\n');print('NKG source iteration association PASS; mutation rejected')
