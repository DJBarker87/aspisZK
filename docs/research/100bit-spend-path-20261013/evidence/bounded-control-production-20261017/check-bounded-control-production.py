from pathlib import Path
import hashlib,json,re,subprocess
repo=Path('/Users/dominic/ZK/.worktrees/100bit-spend-path')
rel=Path('crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs')
production=repo/rel;probe=Path('/tmp/aspis-bounded-control-20261017/src/lib.rs')
s=production.read_text();p=probe.read_text()
def body(src,marker):
 a=src.index('{',src.index(marker));depth=0
 for b in range(a,len(src)):
  depth+=src[b]=='{';depth-=src[b]=='}'
  if depth==0:return src[a:b+1]
 raise ValueError(marker)
actual=body(s,'fn bounded_append_carry(');checked=body(p,'pub fn bounded_carry(')
assert actual==checked
match_start=s.index('    let invalid_amount = match public.withdrawal_amount {')
match_end=s.index('\n    if invalid_amount {',match_start)
actual_guard=s[match_start:match_end].replace('let invalid_amount = match public.withdrawal_amount','match amount').rstrip().removesuffix(';').strip()
checked_guard=body(p,'pub fn invalid_amount(')[1:-1].strip().replace('Some(value)','Some(amount)').replace('value ==','amount ==').replace('value >=','amount >=')
normalize=lambda x:re.sub(r'\s+','',x)
assert normalize(actual_guard)==normalize(checked_guard),(actual_guard,checked_guard)
assert len(re.findall(r'let carry = bounded_append_carry\(',s))==4
assert 'trailing_ones' not in '\n'.join(x for x in s.splitlines() if not x.strip().startswith('///'))
assert '.is_some_and' not in s
record={'production_path':str(rel),'source_revision_before_edit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip(),'production_source_sha256':hashlib.sha256(production.read_bytes()).hexdigest(),'standalone_checked_probe_sha256':hashlib.sha256(probe.read_bytes()).hexdigest(),'carry_helper_body_byte_identical':True,'carry_helper_body_sha256':hashlib.sha256(actual.encode()).hexdigest(),'amount_guard_matches_probe_after_local_rename_and_whitespace':True,'carry_call_sites':4,'production_source_modified':True,'full_modified_crate_reextraction_proved':False,'deployed_artifact_equivalence_proved':False}
Path('/tmp/bounded-control-production-binding.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record,indent=2))
