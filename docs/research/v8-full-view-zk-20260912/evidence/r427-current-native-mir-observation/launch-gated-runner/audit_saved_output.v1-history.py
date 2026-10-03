#!/usr/bin/env python3
"""Read-only R427 diagnostic output audit; no extraction or compiler execution."""
import argparse, copy, hashlib, json, pathlib, re
p=argparse.ArgumentParser()
p.add_argument('--baseline',type=pathlib.Path,required=True)
p.add_argument('--output',type=pathlib.Path,required=True)
p.add_argument('--stderr',type=pathlib.Path,required=True)
p.add_argument('--result',type=pathlib.Path,required=True)
p.add_argument('--gnu-time',type=pathlib.Path,required=True)
p.add_argument('--host-before',type=pathlib.Path,required=True)
p.add_argument('--host-after',type=pathlib.Path,required=True)
p.add_argument('--report',type=pathlib.Path,required=True)
a=p.parse_args()
def sha(x): return hashlib.sha256(x.read_bytes()).hexdigest()
BASE_EXPECTED='399020435e94aaa7135c06d68445e9b936bd22fe6d1e1d197ee708d448d584ae'
TARGET='core::iter::traits::iterator::Iterator::try_fold'
old=json.loads(a.baseline.read_text()); new=json.loads(a.output.read_text())
result=json.loads(a.result.read_text()); host_before=json.loads(a.host_before.read_text()); host_after=json.loads(a.host_after.read_text())
gnu=a.gnu_time.read_text()
def gnu_value(pattern):
 m=re.search(pattern,gnu,re.M); return m.group(1).strip() if m else None
wall=gnu_value(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\):\s*(.+)')
rss=gnu_value(r'Maximum resident set size \(kbytes\):\s*(\d+)')
swaps=gnu_value(r'Swaps:\s*(\d+)')
gnu_status=gnu_value(r'Exit status:\s*(\d+)')
assert wall is not None and rss is not None and swaps is not None and gnu_status is not None, 'incomplete GNU time metrics'
assert int(gnu_status)==result['charon_exit_status']==result['gnu_time_exit_status'], (gnu_status,result['charon_exit_status'],result['gnu_time_exit_status'])
assert wall==result['wall_time'] and int(rss)==result['peak_rss_kib'] and int(swaps)==result['swap_count']
expected_sources={'r110_norm.rs':'8459fc12322811b589f9a9d29bf474f3ee45e58aa13c716b8f324c2db81b160e','circle_norm.rs':'3f0882366674d5d41e365e62787d85b62076e6077697e9f756e135ce12aedbd2','line_norm.rs':'4fb70d37d16053a74e08716433af45998e7ddd13fc5dca7b1c86505ed7e2c528','joined_inverse.rs':'ef9b45ce8a7ffbcf57564bcc1348cae3197a09fbbbd529ffca632b778281efeb','aspis_core_field.rs':'639b6425fe672e0fa6019b99b702d1f08f56cd75c4d9ad6defef854b7640f499','performance_host_Cargo.toml':'62f81cd54314ec1a637c61404bd6cf6f12f8defbf1ab68fb0ded4956df80646c','performance_host_Cargo.lock':'a2e3d525c3a0f01428b56df55001ba304981a6b8c26cca08badf7b09b7029814'}
assert result['source_hashes_before_after']['before']==expected_sources
assert result['source_hashes_before_after']['after']==expected_sources
assert host_before['wrapper_sha256']=='b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c'
assert host_before['caps']=={'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':'0','TasksMax':128}
assert host_before['reviewed_build_receipt_sha256']
assert host_after['source_hashes_after']==host_before['source_hashes_before']
assert host_after['baseline_sha_after']==BASE_EXPECTED
base_hash=sha(a.baseline); out_hash=sha(a.output)
assert base_hash==BASE_EXPECTED, ('baseline checksum mismatch',base_hash)
assert set(old)==set(new)
def keyed(rows):
 m={}; duplicates=[]
 for i,row in enumerate(rows):
  k=json.dumps(row['key'],sort_keys=True,separators=(',',':'),ensure_ascii=False)
  if k in m: duplicates.append(i)
  m[k]=row['value']
 return m,duplicates
old_opts=old['translated']['options']; new_opts=new['translated']['options']
# R427 must not turn on or otherwise change R426's original-ULLBC print option.
assert old_opts.get('print_original_ullbc') is False
assert new_opts.get('print_original_ullbc') is False
changed_opts={k:(old_opts.get(k),new_opts.get(k)) for k in set(old_opts)|set(new_opts) if old_opts.get(k)!=new_opts.get(k)}
assert set(changed_opts)=={'dest_file'}, changed_opts
assert new_opts['dest_file']=='/home/dombarker/project-offloads/aspis-r427-raw-mir-capture-20261002-a/R427RawMirCapture.llbc', new_opts['dest_file']
normalized=copy.deepcopy(new)
normalized['translated']['options']['dest_file']=old_opts['dest_file']
old_sn=old['translated']['short_names']; new_sn=new['translated']['short_names']
old_map,old_dups=keyed(old_sn); new_map,new_dups=keyed(new_sn)
assert len(old_sn)==len(new_sn)==347
assert not old_dups and not new_dups
assert old_map==new_map
normalized['translated']['short_names']=old_sn
exact=normalized==old
stderr=a.stderr.read_text(errors='replace')
begins=list(re.finditer(r'^ASPIS_R427_RAW_MIR_BEGIN name=([^\s]+) def_id=([^\n]+)$',stderr,re.M))
ends=list(re.finditer(r'^ASPIS_R427_RAW_MIR_END name=([^\s]+) def_id=([^\n]+)$',stderr,re.M))
frame=None; frames=[]; frame_errors=[]
if len(begins)==1 and len(ends)==1:
 b,e=begins[0],ends[0]
 if b.start()>=e.start() or b.group(1)!=TARGET or e.group(1)!=TARGET or b.group(2)!=e.group(2):
  frame_errors.append('frame labels, order, or DefId mismatch')
 else:
  frame=stderr[b.start():e.end()]
  frames=[frame]
else: frame_errors.append(f'expected exactly one framed MIR body, saw begin={len(begins)} end={len(ends)}')
required=['ASPIS_R427_STATEMENT_SOURCE','ASPIS_R427_USE_RETAG','ASPIS_R427_TERMINATOR_SOURCE','ASPIS_R427_CALL_ARG']
marker_counts={m:stderr.count(m) for m in required}
if frame is not None:
 for m in required:
  if m not in frame: frame_errors.append(f'missing selected-frame marker {m}')
report={
 'classification':'saved-output diagnostic audit; no compiler, extraction, translation, or Lean run',
 'baseline':{'path':str(a.baseline),'sha256':base_hash},
 'output':{'path':str(a.output),'sha256':out_hash},
 'raw_stderr':{'path':str(a.stderr),'sha256':sha(a.stderr),'bytes':a.stderr.stat().st_size},
 'execution_receipt':{'result_path':str(a.result),'result_sha256':sha(a.result),'gnu_time_path':str(a.gnu_time),'gnu_time_sha256':sha(a.gnu_time),'wall_time':wall,'peak_rss_kib':int(rss),'swaps':int(swaps),'gnu_time_exit_status':int(gnu_status),'host_before_path':str(a.host_before),'host_before_sha256':sha(a.host_before),'host_after_path':str(a.host_after),'host_after_sha256':sha(a.host_after),'caps':host_before['caps'],'source_hashes_match_before_after':host_after['source_hashes_after']==host_before['source_hashes_before'],'baseline_hash_match_before_after':host_after['baseline_sha_after']==BASE_EXPECTED},
 'llbc_equality_gate':{
   'allowed_normalizations':['translated.options.dest_file (must be sole options difference)','translated.short_names order only after unique 347-key map and exact key/value equality'],
   'option_differences':changed_opts,
   'short_names':{'entry_count_baseline':len(old_sn),'entry_count_output':len(new_sn),'unique_baseline':len(old_map),'unique_output':len(new_map),'duplicate_baseline_indices':old_dups,'duplicate_output_indices':new_dups,'key_value_maps_equal':old_map==new_map,'raw_order_equal':old_sn==new_sn},
   'all_other_native_fields_lists_and_order_exact':exact,
   'passed':exact},
 'raw_mir_frame':{'target':TARGET,'begin_count':len(begins),'end_count':len(ends),'def_id':begins[0].group(2) if len(begins)==1 else None,'marker_counts_whole_stderr':marker_counts,'frame_errors':frame_errors,'full_frame_preserved_as':'mir-frame.txt' if frame is not None else None},
 'scope':'An equality and raw observation inventory only. It does not prove how MIR Copy/Retag is lowered, that this MIR is semantically preserved by Rustc/Charon, or any callback/source theorem.'}
a.report.parent.mkdir(parents=True,exist_ok=True)
if frame is not None:
 (a.report.parent/'mir-frame.txt').write_text(frame+'\n')
a.report.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'llbc_gate_passed':exact,'frame_errors':frame_errors,'report':str(a.report)},indent=2))
# Preserve report and frame even on failure; return a failed audit status for caller-controlled history.
raise SystemExit(0 if exact and frame is not None and not frame_errors else 2)
