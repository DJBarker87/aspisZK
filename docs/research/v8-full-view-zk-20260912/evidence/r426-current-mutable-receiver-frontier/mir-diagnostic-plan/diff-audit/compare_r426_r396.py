#!/usr/bin/env python3
"""Strict R426 vs R396 decoded LLBC comparison; recognizes only ShortNames as keyed map."""
import argparse, copy, hashlib, json, pathlib
ROOT=pathlib.Path(__file__).resolve().parents[4]
DEFAULT_OLD=ROOT/'.r21-scratch/r396-private-batch-unmonomorphized-plan/R396PrivateBatchUnmonomorphized.llbc'
DEFAULT_NEW=ROOT/'.r21-scratch/r426-mutable-borrow-copy-frontier/mir-diagnostic-plan/R426OriginalUllbc.llbc'
DEFAULT_OUT=pathlib.Path(__file__).resolve().parent
parser=argparse.ArgumentParser()
parser.add_argument('--old',type=pathlib.Path,default=DEFAULT_OLD,help='saved R396 baseline LLBC JSON')
parser.add_argument('--new',type=pathlib.Path,default=DEFAULT_NEW,help='saved R426 LLBC JSON')
parser.add_argument('--out',type=pathlib.Path,default=DEFAULT_OUT,help='write raw diff report and leaf differences here')
args=parser.parse_args()
OLD=args.old.resolve(); NEW=args.new.resolve(); OUT=args.out.resolve(); OUT.mkdir(parents=True,exist_ok=True)
def display_path(p):
 try: return p.relative_to(ROOT).as_posix()
 except ValueError: return str(p)
EXPECTED={'old':'399020435e94aaa7135c06d68445e9b936bd22fe6d1e1d197ee708d448d584ae','new':'ed43306eac05443a2f4f91121ba8e943a000a66b0d7273eabc40735c64c6f15d'}
SOURCE_EXPECTED={
 'ast/mod.rs':'39a95255923d7ac08cfbdd6a7197a0ac48f2bf2dcdd01926b81c21a3289ac496',
 'ast/krate.rs':'72b774a05f1e5de3b64e504376c35f6045f12b934943b96c330f0536aa211d23',
 'common.rs':'44426b91231516d286c5f69fb8424468e8fbbeee8977ed584e1e4a72b90dea32',
 'transform/add_missing_info/compute_short_names.rs':'dea4fff203bb41ebd459657ff32d664dbd07468b01d8d7e50ca657e4792ca8b1',
}
SOURCE_BASE=pathlib.Path(__file__).resolve().parents[1]/'source/pinned-charon/src'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def canon(v): return json.dumps(v,sort_keys=True,separators=(',',':'),ensure_ascii=False)
def walk_diffs(a,b,path='$'):
 if type(a) is not type(b):
  yield {'path':path,'old':a,'new':b,'shape':'type'}
 elif isinstance(a,dict):
  if set(a)!=set(b): yield {'path':path,'old_keys':sorted(a),'new_keys':sorted(b),'shape':'keys'}
  for k in sorted(set(a)&set(b)): yield from walk_diffs(a[k],b[k],path+'/'+str(k))
 elif isinstance(a,list):
  if len(a)!=len(b): yield {'path':path,'old_length':len(a),'new_length':len(b),'shape':'length'}
  for i,(x,y) in enumerate(zip(a,b)): yield from walk_diffs(x,y,path+'/'+str(i))
 elif a!=b:
  yield {'path':path,'old':a,'new':b,'shape':'value'}

def keyed_short_names(rows,label):
 out={}; duplicate=[]
 for i,row in enumerate(rows):
  key=canon(row['key'])
  if key in out: duplicate.append({'index':i,'key':row['key']})
  out[key]=row['value']
 return out,duplicate
assert sha(OLD)==EXPECTED['old'],('old input hash',sha(OLD))
assert sha(NEW)==EXPECTED['new'],('new input hash',sha(NEW))
source_hashes={rel:sha(SOURCE_BASE/rel) for rel in SOURCE_EXPECTED}
assert source_hashes==SOURCE_EXPECTED,('pinned Charon source hashes',source_hashes)
a=json.loads(OLD.read_text());b=json.loads(NEW.read_text())
assert set(a)==set(b)
# First preserve and classify every raw decoded-JSON leaf difference.
diffs=list(walk_diffs(a,b))
# The only allowed options are the fresh output destination and enabled debug print flag.
ao=a['translated']['options'];bo=b['translated']['options']
option_diffs=list(walk_diffs(ao,bo,'translated/options'))
assert {d['path'].removeprefix('translated/options/').split('/')[0] for d in option_diffs}=={'dest_file','print_original_ullbc'}
assert len(option_diffs)==2 and all(d['shape']=='value' for d in option_diffs)
assert ao['dest_file']=='/home/dombarker/project-offloads/aspis-r396-private-batch-unmonomorphized-20261002-a/R396PrivateBatchUnmonomorphized.llbc'
assert bo['dest_file']=='/home/dombarker/project-offloads/aspis-r426-original-ullbc-20261002-a/R426OriginalUllbc.llbc'
assert ao['print_original_ullbc'] is False and bo['print_original_ullbc'] is True
normalized=copy.deepcopy(b)
for k in ('dest_file','print_original_ullbc'): normalized['translated']['options'][k]=ao[k]
# Do not sort lists generally: remove only this source-declared map field for remaining native equality.
old_sn=a['translated']['short_names'];new_sn=b['translated']['short_names']
old_map,old_dups=keyed_short_names(old_sn,'R396');new_map,new_dups=keyed_short_names(new_sn,'R426')
assert not old_dups and not new_dups
assert len(old_sn)==len(new_sn)==347
assert old_map==new_map
normalized['translated']['short_names']=old_sn
assert normalized==a
# Locate all raw changed map positions and record both exact key/value rows; no rows are dropped.
changed_positions=[i for i,(x,y) in enumerate(zip(old_sn,new_sn)) if x!=y]
map_mismatches=[]
for i in changed_positions:
 x,y=old_sn[i],new_sn[i]
 assert canon(x['key'])==canon(y['key']) or old_map.get(canon(x['key']))==new_map.get(canon(x['key']))
 map_mismatches.append({'index':i,'R396_row':x,'R426_row':y,'R396_key':x['key'],'R426_key':y['key']})
map_report={'entry_count_R396':len(old_sn),'entry_count_R426':len(new_sn),'unique_key_count_R396':len(old_map),'unique_key_count_R426':len(new_map),'duplicate_keys_R396':old_dups,'duplicate_keys_R426':new_dups,'keys_equal':set(old_map)==set(new_map),'values_equal_by_key':old_map==new_map,'raw_order_equal':old_sn==new_sn,'raw_changed_positions':len(changed_positions),'first_changed_index':changed_positions[0] if changed_positions else None,'last_changed_index':changed_positions[-1] if changed_positions else None,'changed_positions':changed_positions,'row_diffs':map_mismatches}
# Every changed path in the remaining groups is included with exact values.
other=[]
for d in diffs:
 if d['path'].startswith('$/translated/options/') or d['path'].startswith('$/translated/short_names/'):
  continue
 other.append(d)
report={'classification':'read-only decoded JSON comparison; no LLBC mutation, extraction, translation, or build',
 'inputs':{'R396':{'path':display_path(OLD),'sha256':sha(OLD),'charon_version':a.get('charon_version')},'R426':{'path':display_path(NEW),'sha256':sha(NEW),'charon_version':b.get('charon_version')}},
 'preserved_runner_gate_failure':'diff-audit/history/runner-result-comparison-failure.json is the byte-copy of the original runner result; it records Charon exit 0 and comparison false after the runner’s original strict raw-list comparison.',
 'raw_diff_summary':{'top_level_changed_keys':[k for k in a if a[k]!=b[k]],'translated_changed_groups':[k for k in a['translated'] if a['translated'][k]!=b['translated'][k]],'raw_leaf_difference_count':len(diffs),'translated_options_leaf_differences':option_diffs,'translated_short_names_map':map_report,'all_other_raw_leaf_differences':other},
 'justification_sources':{'charon_source_commit':'cb50ff16b9f1066b8a97dc06da704de2da2fa41c','charon_binary_sha256':'b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c','source_file_sha256':source_hashes,'short_names_field':'../source/pinned-charon/src/ast/krate.rs:266-268; type SeqHashMap<ItemId, Name>, field comment says keyed by items; serde adapter SeqHashMapToArray','map_alias':'../source/pinned-charon/src/ast/mod.rs:30; SeqHashMap is indexmap::IndexMap','lookup':'../source/pinned-charon/src/ast/krate.rs:318-323; item_short_name uses short_names.get(&id), fallback item_name(id)','serialization':'../source/pinned-charon/src/common.rs:224-250; serializes map.into_iter() to array of key/value records; deserializer inserts records into IndexMap at lines254-286','ordering_creation':'../source/pinned-charon/src/transform/add_missing_info/compute_short_names.rs:47-49 uses std HashMap; lines87-99 iterates it and inserts candidate short names into the IndexMap, making serialized order reflect that iteration order','no_global_sort':'Only translated.short_names was converted to a key/value lookup for this audit; all other JSON lists, including item/type/function/ordered-declaration lists and AST fields, were compared in original order.'},
 'strict_comparison_result':{'options_equal_after_exact_two_field_normalization':True,'short_names_equal_as_unique_keyed_map':old_map==new_map and not old_dups and not new_dups,'all_other_fields_exact_including_order':not other,'whole_decoded_llbc_equal_under_these_field_specific_normalizations':True,'normalizations':['translated.options.dest_file (exact expected before/after values asserted)','translated.options.print_original_ullbc (false→true asserted)','translated.short_names order only; all 347 unique key/value entries retained and compared exactly']},
 'boundary':'This is an equality inventory using the pinned native field type and access/serialization code. It does not decide whether the lead should accept this comparison boundary.'}
(OUT/'raw-comparison-and-map-audit.json').write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
(OUT/'raw-leaf-diffs.json').write_text(json.dumps(diffs,indent=2,sort_keys=True)+'\n')
print(json.dumps({'raw_leaf_differences':len(diffs),'options':option_diffs,'short_names':{k:v for k,v in map_report.items() if k not in ('row_diffs','changed_positions')},'other_raw_differences':other,'report':str(OUT/'raw-comparison-and-map-audit.json')},indent=2))
