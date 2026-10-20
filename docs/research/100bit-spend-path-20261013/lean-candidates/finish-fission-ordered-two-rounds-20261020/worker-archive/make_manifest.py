from pathlib import Path
import hashlib, json
root=Path(__file__).resolve().parent
proofs={
 'FinishRoundSelectorSemanticV1':'selector',
 'FinishRoundAlphaSemanticV1':'alpha',
 'FinishFissionHelperAdapterV2':'adapter',
 'FissionLoopStepSemanticsV1':'loop_semantics',
 'FinishFissionHelperLoopV2':'loop',
 'FinishCandidateRoundSuccess':'round_success',
 'FinishCandidateExplicitOps':'explicit_ops',
 'FinishCandidateOuterSuccess':'outer_success',
 'FinishCandidateEquations':'equations',
 'FinishFissionSourceSuccessJoinV3':'source_join',
 'FinishFissionLiteralRangeV1':'literal_ranges',
}
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
modules=[]
for name, folder in proofs.items():
 d=root/'evidence'/folder
 pre=json.loads((d/'preflight.json').read_text())
 rec=json.loads((d/'receipt.json').read_text())
 modules.append({'module':name,'source_sha256':pre['source_sha256'],'object_sha256':rec['object_sha256'],'exit_status':rec['exit_status'],'wall_seconds':rec['wall_seconds'],'peak_process_rss_kib':rec['peak_process_rss_kib'],'scope_memory_peak_bytes':rec['scope_memory_peak_bytes'],'scope_swap_peak_bytes':rec['scope_swap_peak_bytes'],'direct_imports':pre.get('direct_imports',{}),'preflight':str((d/'preflight.json').relative_to(root)),'receipt':str((d/'receipt.json').relative_to(root)),'command':str((d/'command.json').relative_to(root)),'time_log':str((d/'time.log').relative_to(root)),'lean_log':str((d/'lean.log').relative_to(root))})
files=[]
for p in sorted(root.rglob('*')):
 if not p.is_file() or p.name in {'manifest.json','SHA256SUMS.txt'}: continue
 files.append({'path':str(p.relative_to(root)),'sha256':sha(p),'size_bytes':p.stat().st_size})
manifest={'schema':'finish-fission-v2-literal-range-packet-v1','classification':'candidate source model; no production reachability or source adoption claim','selected_modules':modules,'generated_helper_extraction':{'candidate_rust_source_sha256':'a222c9f1a4da189e5123e324a6586c95d31b10cf63fb1cba61686c0a6928b6f8','candidate_rust_function_sha256':'e664741d2208bac1355c5b53e8f367dc50c7d70e08ffc6ca4e7bf27a629ca943','generated_funs_sha256':'7e03477e64f5ea5c732fe40f65f07fb4e7a79bcc422e8c9e1eb3838696bbfbe9','generated_types_sha256':'19da6a50973ae5c22088bda38d6c382ed5ae802c5b359dbb5dd8492e76066435','charon_receipt': 'extraction/runs/charon-a/receipt.json','aeneas_receipt':'extraction/runs/aeneas-a/receipt.json','whole_body_checker':'sources/check_finish_round_helper_adapter_v2.py','checker_result':'PASS; complete mapped generated body equals V2 adapter body'},'superseded':{'V1_adapter_source_sha256':'dc831c6b0b15b0f315ed466dc9ea87673cfae1d20cf51403174f5c5bb2a4106b','V1_adapter_object_sha256':'aade6e2483ccf56a75e37e3f7e45099eac68edd1e4d23e72352ec534e2611b1c','reason':'eager alpha array read before comparison guard; excluded from selected closure'},'files':files}
(root/'manifest.json').write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n')
rows=[]
for p in sorted(root.rglob('*')):
 if p.is_file() and p.name!='SHA256SUMS.txt': rows.append(f'{sha(p)}  {p.relative_to(root)}')
(root/'SHA256SUMS.txt').write_text('\n'.join(rows)+'\n')
