#!/usr/bin/env python3
"""Supplement exact MIR diff with explicit pretty-printer alias normalization.
This is textual comparison, never semantic equivalence or instance pairing.
"""
import collections,hashlib,json,re,difflib
from pathlib import Path
H=Path('/home/dombarker/project-offloads/codex-cx-s10-repin2-20261023');P=H.parent/'codex-cx-s10-repin-20261022'
ns={};exec((H/'diff-host.py').read_text().split('oldelf=')[0],ns)
def canonical(s):
 s=ns['normalize'](s)
 for a,b in [('solana_program::program_error::ProgramError','ProgramError'),('__AccountInfo','AccountInfo'),('__Pubkey','Pubkey'),('std::boxed::Box','Box'),('r1_pool_adapter::','')]:s=s.replace(a,b)
 for name in ['validate_verifier_policy_v1','decode_verifier_registry_v2','decode_verifier_registry_entry_v2','decode_verifier_registry_v1','decode_verifier_registry_entry_v1','encode_pool_v1_pair_verified_afterstate_v1','validate_pool_v1_pair_forest_terminal_statement_v1','decode_pool_v1_pair_forest_terminal_request_v1','pool_v1_pair_forest_output_lane_v1']:
  s=s.replace('aspis_statement::pool_v1::'+name,name)
 for a,b in [('aspis_r1_cost_probe::transport::Variant','Variant'),('solana_program::solana_clock::Clock','Clock'),('solana_program::sysvar::Sysvar','Sysvar')]:s=s.replace(a,b)
 s=re.sub(r'aspis_statement::pool_v1::(PoolV1\w+)',r'\1',s)
 return s
out=[]
for mode,old,new in [('default','build-default-v2','build-default-v3'),('devnet','build-devnet-v1','build-devnet-v2'),('pool','build-pool-v1','build-pool-v1')]:
 a=ns['functions'](P/old);b=ns['functions'](H/new)
 def groups(rows):
  g=collections.defaultdict(list)
  for r in rows:g[r['crate']+':'+canonical(r['header'])].append(r)
  return g
 aa=groups(a);bb=groups(b);changes=[];equal=[]
 for key in sorted(aa.keys()|bb.keys()):
  left=aa[key];right=bb[key]
  hashes=lambda rows:collections.Counter(hashlib.sha256(canonical(r['body']).encode()).hexdigest() for r in rows)
  entry=dict(key=key,old=[ns['short'](r) for r in left],new=[ns['short'](r) for r in right],ambiguous=len(left)>1 or len(right)>1)
  if hashes(left)==hashes(right):
   if collections.Counter(r['sha256'] for r in left)!=collections.Counter(r['sha256'] for r in right):equal.append(entry)
  else:
   if len(left)==len(right)==1:entry['canonical_text_diff']='\n'.join(difflib.unified_diff(canonical(left[0]['body']).splitlines(),canonical(right[0]['body']).splitlines(),n=1))
   changes.append(entry)
 out.append(dict(mode=mode,remaining_changes=changes,alias_or_coordinate_only=equal))
x=dict(modes=out,normalization='Only workspace/source coordinates and explicit MIR pretty-printer spellings: ProgramError qualification, __AccountInfo/AccountInfo, __Pubkey/Pubkey, std::boxed::Box/Box, r1_pool_adapter module qualification, aspis_statement::pool_v1 direct PoolV1 type qualification. Plus explicitly listed Variant/Clock/Sysvar and nine statement helper qualifications. Exact diff remains authoritative. Duplicate keys remain lists; no semantic instance pairing.',scope='Text equality after documented substitutions only; source child equality independently follows from pinned source files. No compiler semantic proof.')
(H/'alias-mir-diff.json').write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
print(json.dumps([dict(mode=r['mode'],remaining=len(r['remaining_changes']),alias_or_coordinate_only=len(r['alias_or_coordinate_only'])) for r in out]))
