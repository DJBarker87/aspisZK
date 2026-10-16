#!/usr/bin/env python3
"""Exact Git-only decoder correspondence; no extraction or compiler replay."""
from pathlib import Path
import argparse,hashlib,importlib.util,json,subprocess,tempfile
here=Path(__file__).resolve().parent;root=here.parents[4]
sha=lambda b:hashlib.sha256(b).hexdigest()
revisions=['0626294e34632812accf4cb14704f027368ea871',
 'b92ab28465f9ffd4edcd3e2d5300cc9306ba66af','0ff133effe7ee299186700c2a91a35d5548b0ca5']
parser_path='docs/research/100bit-spend-path-20261013/tools/public-serializer-extraction-kit/extract.py'
spec=importlib.util.spec_from_file_location('cuts',root/parser_path);cuts=importlib.util.module_from_spec(spec);spec.loader.exec_module(cuts)
groups={
 'crates/aspis-core/src/field.rs':['from_le_bytes(bytes: [u8; 4])'],
 'crates/aspis-statement/src/atomic_statement.rs':['unwrap_fixed_slice<T: Copy>','decode_digest_canonical('],
 'crates/aspis-statement/src/pool_v1/pair_terminal.rs':['decode_pool_v1_pair_verified_afterstate_v1('],
 'crates/aspis-statement/src/pool_v1/pair_tree_profile.rs':['decode_pair_afterstate_boxed_v1(',
  'decode_pool_v1_pair_live_snapshot_v1(','decode_pair_live_snapshot_boxed_v1(',
  'decode_pool_v1_pair_late_public_statement_boxed_v1('],
 'crates/aspis-statement/src/pool_v1/payment_relation.rs':['decode_common(',
  'decode_pool_v1_private_transfer_public_v1(','decode_pool_v1_withdrawal_public_v1('],
 'crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs':['decode_lane_transition_boxed_v1(',
  'decode_terminal_common_boxed_v1(','decode_transfer_statement_boxed_v1(',
  'decode_withdrawal_statement_boxed_v1(','decode_pool_v1_pair_forest_terminal_statement_v1(',
  'validate_pool_v1_pair_forest_terminal_statement_v1(']}
blob=lambda rev,path:subprocess.check_output(['git','-C',str(root),'show',rev+':'+path])
full={};records=[];removed={}
with tempfile.TemporaryDirectory(prefix='decoder-correspondence-') as temp:
 for path,anchors in groups.items():
  raw={rev:blob(rev,path) for rev in revisions}
  full[path]={rev:sha(b) for rev,b in raw.items()}
  assert raw[revisions[1]]==raw[revisions[2]],path
  for anchor in anchors:
   entries={};bodies=[]
   for rev,b in raw.items():
    f=Path(temp)/'source.rs';f.write_bytes(b)
    body,start,end,line,last=cuts.find_item(f,'fn '+anchor)
    assert b[start:end]==body;bodies.append(body)
    entries[rev]={'start_byte':start,'end_byte_exclusive':end,'start_line':line,
     'end_line_exclusive':last,'sha256':sha(body)}
   assert bodies[0]==bodies[1]==bodies[2],anchor
   records.append({'file':path,'anchor':'fn '+anchor,'versions':entries})
  if path.endswith('/pair_forest_terminal.rs'):
   current=raw[revisions[1]];f=Path(temp)/'source.rs';f.write_bytes(current)
   body,start,end,_,_=cuts.find_item(f,'pub fn semantic_public(&self)')
   assert current[end:end+2]==b'\n\n';end+=2
   assert current[:start]+current[end:]==raw[revisions[0]]
   removed={'start_byte':start,'end_byte_exclusive':end,'added_bytes_sha256':sha(current[start:end]),
    'inverse_exact_full_file':True}
  else:assert raw[revisions[0]]==raw[revisions[1]],path
assert len(records)==17
result={'revisions':revisions,'whole_file_hashes':full,'declarations':records,
 'selector_only_terminal_file_addition':removed,'source_cut_parser':{'path':parser_path,'sha256':sha((root/parser_path).read_bytes())},
 'scope':'Six direct source files: five fully unchanged since062; terminal file differs only by exact added selector. Sixteen audited decoder/root helper declarations plus actual terminal validator are byte-identical at all three revisions. This is source correspondence, not a new historical compile, Rust/backend refinement or actual caller execution theorem.'}
p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args()
out=here/'decoder-source-correspondence.json'
if a.check:assert json.loads(out.read_text())==result
else:out.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print('PASS17 exact declarations/6 direct files at062,b92,0ff; original whole-file differences retained')
