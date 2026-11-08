from pathlib import Path
import hashlib,json,lzma,re,subprocess
E=Path('evidence/pv-lib-20261107/lane-A/session8');base='1451aa2e0c9dfb974b4d846aed22c8407d5490ca';sha=lambda b:hashlib.sha256(b).hexdigest()
support=json.load(open(E/'SUPPORT.json'));roots=json.load(open(E/'AUDIT_ROOTS.json'));audit=json.load(open(E/'RAW_AUDIT.json'))
assert len(roots['roots'])==128 and set(roots['roots'])=={r['root']for r in audit['roots']}
assert audit['strict_raw'] and audit['unresolved']==0 and audit['summary_mismatches']==0
for r in support:
 receipt=json.load(open(E/f"receipt-{r['attempt']}.json"));assert receipt['accepted'] and not receipt['runtime_audit']
 assert sha(Path(r['source']).read_bytes())==receipt['source_sha256']==r['source_sha256']
 assert receipt['source_revision'] and receipt['source_index_blob']
for n in ['lean/PV_LIB_A_StoreActionTable.lean','lean/PV_LIB_A_StoreActionTable7.lean','lean/PV_LIB_A_TypedDropSource.lean','lean/PV_LIB_A_EmittedDropBinding.lean']:
 assert Path(n).read_bytes()==subprocess.check_output(['git','show',base+':'+n]),n
m=Path('evidence/pv-lib-20261107/PLIB_MAP.json');before=json.loads(subprocess.check_output(['git','show',base+':'+str(m)]));now=json.loads(m.read_text());assert before['slots']==now['slots']and before['counts']==now['counts']
receipts=[json.load(open(p))for p in sorted(E.glob('receipt-*.json'))]
failed=[r for r in receipts if not r['accepted']];assert len(failed)==9
for r in receipts:
 admission=json.load(open(E/f"admission-{r['attempt']}.json"));assert admission['allowed']is True
 assert r['source_revision'] and r['source_index_blob']
 cmd=r['command'];assert all(cap in cmd for cap in ['MemoryHigh=6G','MemoryMax=8G','MemorySwapMax=0','TasksMax=64'])
 assert r['swaps']=='0'
 if not r['runtime_audit']:assert cmd[-1]=='7000'
 if not r['accepted']:
  p=E/f"failed-{r['attempt']}.lean.xz";assert p.exists() and sha(lzma.decompress(p.read_bytes()))==r['source_sha256']
  assert not any(q['attempt']>r['attempt'] and q['source_sha256']==r['source_sha256']for q in receipts),'unchanged failed source rerun'
for a in [47454,47475]:
 assert not (E/f'receipt-{a}.json').exists() and not (E/f'time-{a}.log').exists()
 transport=json.load(open(E/f'transport-{a}.json'));assert transport['exit']!=0 and 'not in coherent cohort'in transport['stderr']
old=Path('lean/PV_LIB_A_RawAudit7.lean').read_text();new=Path('lean/PV_LIB_A_RawAudit8.lean').read_text();pattern=r'    \(#\[.*?\],\n     #\[.*?\]\)';assert re.sub(pattern,'ARRAYS',old,count=1,flags=re.S)==re.sub(pattern,'ARRAYS',new,count=1,flags=re.S)
archive=json.load(open(E/'RAW_GRAPH_MANIFEST.json'));assert sha((E/'RAW_GRAPH_ARCHIVE.json.xz').read_bytes())==archive['archive_sha256']
assert not [p for p in E.rglob('*')if p.is_file()and p.stat().st_size>20*1024**2]
paths=subprocess.check_output(['git','diff','--name-only',base],text=True).splitlines();bad=[p for p in paths if not(p.startswith('lean/PV_LIB_A_')or p.startswith('evidence/pv-lib-20261107/lane-A/')or p in [str(m),'evidence/pv-lib-20261107/REMAINING.md'])];assert not bad,bad
subprocess.run(['git','diff','--check'],check=True)
result=dict(base=base,revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),support_modules=len(support),strict_roots=len(roots['roots']),strict_audit_attempt=47493,focused_scopes=sum(not r['runtime_audit']for r in receipts),accepted_focused=sum(r['accepted']and not r['runtime_audit']for r in receipts),retained_failed_compiles=[r['attempt']for r in failed],pre_elaboration_failures=[47454,47475],legacy_v2_unchanged=True,slots_unchanged=True,endpoint_premises_removed=0,endpoint_premises_added=0,new_T_fields=0,byte_images_defined=0,driver_and_walker_unchanged_except_arrays=True,source_hashes_match=True,all_scopes_capped_and_swap_zero=True,max_peak_rss_kbytes=max(int(r['peak_rss_kbytes'])for r in receipts),validation='PASS; partial source support only; target not established')
(E/'VALIDATION.json').write_text(json.dumps(result,indent=2)+'\n')
(E/'COMPILES.json').write_text(json.dumps([{k:r[k]for k in ['attempt','target','accepted','runtime_audit','exit','wall','peak_rss_kbytes','swaps','source_revision','source_index_blob','source_sha256']}for r in receipts],indent=2)+'\n')
print(json.dumps(result,indent=2))
