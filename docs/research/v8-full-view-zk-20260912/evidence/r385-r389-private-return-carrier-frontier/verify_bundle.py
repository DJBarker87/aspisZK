#!/usr/bin/env python3
"""Portable integrity and diagnostic-result checks for the R385/R389 bundle."""
import hashlib, json, re
from pathlib import Path

HERE = Path(__file__).resolve().parent

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def gnu(path):
    text = path.read_text(errors='replace')
    wall = re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([^\n]+)', text)
    rss = re.search(r'Maximum resident set size \(kbytes\): (\d+)', text)
    swap = re.search(r'Swaps: (\d+)', text)
    status = re.search(r'Exit status: (\d+)', text)
    assert wall and rss and swap and status, path
    return {'wall': wall.group(1), 'rss_kib': int(rss.group(1)), 'swaps': int(swap.group(1)), 'exit': int(status.group(1))}

manifest = HERE / 'SHA256SUMS'
expected = {}
for line in manifest.read_text().splitlines():
    digest, name = line.split('  ', 1)
    expected[name] = digest
actual_files = {p.relative_to(HERE).as_posix() for p in HERE.rglob('*') if p.is_file() and p != manifest}
assert actual_files == set(expected), {'missing': sorted(set(expected)-actual_files), 'unlisted': sorted(actual_files-set(expected))}
for name, digest in expected.items():
    assert sha(HERE / name) == digest, name

parent = HERE / 'compiler/source/PrePasses.parent.ml'
v1 = HERE / 'compiler/source/PrePasses.v1-failed.ml'
v2 = HERE / 'compiler/source/PrePasses.v2-built.ml'
assert sha(parent) == '09014aa93bffd2cafeebaf23d27a301d66986d9349f4cc9dca6e8d1dfe0ba7dd'
assert sha(v1) == 'ea353ee571da9d5c00f5fa6bc7041954eb3c10b3ac5abe9798d1b3bdbcafcb75'
assert sha(v2) == '579f332212ad75b386b088ef7835783f7cb84a835b1acb96031d49847fc53a17'
assert v1.read_bytes().count(b'(TypeId id, name)') == 2
assert v2.read_bytes() == v1.read_bytes().replace(b'(TypeId id, name)', b'(IdType id, name)')
assert sha(HERE / 'compiler/source/NameMatcher.ml') == 'bdafe5b3f4a688d0fa0b4df7f2e8a3d907f70be9fdaf64420ea600ceab597aa8'
assert sha(HERE / 'compiler/source/LlbcAstUtils.ml') == '17cb1b5cd3e0cf119f4c4eee776e0fc49e2a39c6ee7abbaa339f70d466484b97'

v1_result=json.loads((HERE/'compiler/builds/v1-failed/build-result.json').read_text())
v2_result=json.loads((HERE/'compiler/builds/v2-built/build-result.json').read_text())
v1_gnu=gnu(HERE/'compiler/builds/v1-failed/compiler-gnu-time.txt')
v2_gnu=gnu(HERE/'compiler/builds/v2-built/compiler-gnu-time.txt')
assert v1_result['build_exit_status']==1 and v1_gnu=={'wall':'0:03.25','rss_kib':502444,'swaps':0,'exit':1}
assert v2_result['build_exit_status']==0 and v2_gnu=={'wall':'0:06.69','rss_kib':502864,'swaps':0,'exit':0}
assert v2_result['sampled_container_memory_peak_bytes']==564842496
assert v2_result['sampled_container_memory_swap_peak_bytes']==0
assert v2_result['binary_sha256']=='f12977c5acd368d268d3af9562110ab29be60d7b4055dde937d0049f85409db5'
assert 'no constructor' in (HERE/'compiler/builds/v1-failed/build.log').read_text()
caps=json.loads((HERE/'compiler/R385-v2-build-plan.json').read_text())['runner']['caps']
assert caps['MemoryHigh']=='5G' and caps['MemoryMax']=='7G' and caps['MemorySwapMax']=='0' and caps['TasksMax']==128
assert caps['docker_memory_swap']=='7g (equal; no swap)'
expected_src=sorted(json.loads((HERE/'compiler/expected-nonbuild-source-manifest.json').read_text())['rows'],key=lambda x:x['path'])
actual_src=sorted(json.loads((HERE/'compiler/observed-nonbuild-source-manifest.json').read_text())['rows'],key=lambda x:x['path'])
assert expected_src==actual_src
audit=json.loads((HERE/'compiler/postbuild-source-audit.json').read_text())
assert audit['status']=='PASS' and audit['exact_path_kind_content_size_mode_match'] is True and audit['expected_nonbuild_paths']==115

input_path=HERE/'input/R327PrivateBatchSourceTryFold.llbc'
assert sha(input_path)=='9ed7c0ab91051ac61d812d66651680112ac26fe907faa76f9d4d2d9a14d03442'
raw=json.loads(input_path.read_text()); tr=raw['translated']
assert raw['has_errors'] is False
assert len(tr['fun_decls'])==54 and sum(x is not None for x in tr['fun_decls'])==53
assert len(tr['type_decls'])==29
options=[x for x in tr['type_decls'] if isinstance(x,dict) and x['item_meta'].get('lang_item')=='Option']
assert [x['def_id'] for x in options]==[9,12,13]
assert all([v['name'] for v in x['kind']['Enum']]==['None','Some'] for x in options)
rows=json.loads((HERE/'input/selected-try-fold-rows-36-38.json').read_text())['rows']
assert [x['def_id'] for x in rows]==[36,38]
assert all(x['metadata']['span']['data']['beg']['line']==2486 and x['metadata']['span']['data']['end']['line']==2490 for x in rows)

r389=HERE/'translation/output'
result=json.loads((r389/'result.json').read_text())
metrics=json.loads((r389/'translation-result.json').read_text())
log=(r389/'translate.log').read_text()
run=gnu(r389/'translate.log')
assert result['translator_exit_status']==2 and metrics['translator_exit_status']==2
assert run=={'wall':'0:00.21','rss_kib':68464,'swaps':0,'exit':2}
assert 'Unexpected erased region' in log and '2486:4-2490:35' in log
assert 'SymbolicToPureTypes.ml, line 848' in log
assert metrics['generated_dir_exists'] is False and metrics['translation_json_exists'] is False
assert metrics['required_batch_root_manifest_matches']==0 and metrics['root_in_lean_source'] is False
assert not (r389/'external_template_axioms').exists()
assert (HERE/'translation/output/translation-result.json').exists()
launch=json.loads((HERE/'translation/launch/launch-result.json').read_text())
payload=HERE/'translation/launch/remote_translate.py'
assert sha(payload)==launch['remote_payload_sha256']
assert launch['launcher_exit_status']==2 and launch['scp_exit_status']==0
assert result['R327_source_revision']=='d4bf07b08443136de0a11fc1fd932bd604586c2e'
assert result['translation_launch_revision']==launch['launch_revision']=='0910b78908f2bc7194da93514d20831dea1f9940'
assert result['source_sha256']=='9ed7c0ab91051ac61d812d66651680112ac26fe907faa76f9d4d2d9a14d03442'
assert result['binary_sha256']=='f12977c5acd368d268d3af9562110ab29be60d7b4055dde937d0049f85409db5'

source_file=HERE/'translation/SymbolicToPureTypes.pinned.ml'
assert sha(source_file)=='29f4a784b0edb1dccf895aba78ec6d5c15c081e8602f7778db264b21272c54a0'
snippet=(HERE/'translation/SymbolicToPureTypes-erased-region-excerpt.txt').read_text()
assert 'gid = get_region_group r' in snippet and 'RErased -> [%craise_opt_span] span "Unexpected erased region"' in snippet

print(json.dumps({
  'status':'PASS', 'files_hashed':len(expected), 'v1_build':v1_gnu, 'v2_build':v2_gnu,
  'v2_container_peak_bytes':v2_result['sampled_container_memory_peak_bytes'],
  'R327_sha256':sha(input_path), 'R327_counts':{'function_rows':54,'nonnull_functions':53,'type_declarations':29,'Option_ids':[9,12,13]},
  'R389_translation':run, 'R389_failure':'Unexpected erased region at iterator.rs 2486:4-2490:35; SymbolicToPureTypes.ml 848',
  'R389_root_emitted':False,'template_inventory':'N/A; generated directory absent'
},indent=2))
