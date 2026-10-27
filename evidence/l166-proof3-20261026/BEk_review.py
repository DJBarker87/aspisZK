"""Task-only distinct statement/trust-boundary inventories; no release replay."""
from pathlib import Path
import re,json,subprocess,sys
P=Path(__file__).resolve().parent;R=P.parents[1]
selection={
'S2W_ExtractionBoundary':'First Second AeneasExtraction P1 RuntimeSyscall accepted_native_observation native_first_fields',
'S2W_DigestExtraction':'AeneasExtraction native_binding sourceBoundary',
'S2W_D189Entry':'Record Entry',
'S2W_D189Wrappers':'Allocator first second',
'Port4B_BatchJoin':'initial compose accepted',
'Port4B_TreeJoin':'PackedKeys accepted',
'Port4B_StageRows':'PreparedBinding tx1 tx2',
'Port4B_Install':'leaves',
'Port9OR_Batch':'code values source',
'Op5T_SamePair':'dictionary batches',
'SdkC_BatchSource':'code currentCode stageCode erasure',
'SdkC_BatchPair':'Returning same_pair accepted_pair',
'SdkC_Source':'Query readLog run associated',
'SdkC_Oracle':'program accepted_exact',
'BEh_Scope':'AcceptedPath RejectedPrefix BothSlots Law logs',
'BEi_Execution':'Executes sound',
'BEi_ExecutionComplete':'complete',
'BEi_RecorderCut':'issued source_cut',
'BEj_ReifiedBatch':'programs of_steps reified_observation',
'BEj_SlotExport':'Prefix current stage',
'BEj_ErasedBoundaryGap':'installed retained',
'RPx_Transport':'transport charged',
'RPx_AccountCharge':'charged',
'ARS_Coverage':'SupportedEntry',
'ARS_QueryTransport':'Agrees covered exact',
'ARU_Support':'At',
'ARU_OriginalFactory':'original',
'ARU_CutsOrigin':'selected',
'ARU_Carrier':'exact',
'ARU_Join':'accepted',
'ARU_Charges':'charged',
'ARU_OriginalLaw':'exact',
'ARU_CoverageQuantifiers':'exact_iff',
'ARU_RootRestriction':'impossible_if_native',
'ARU_Nonvacuity':'conditional',
'ARV_UniversalRefutation':'',
}
items=[]
for mod,names in selection.items():
 path=R/'lean'/(mod+'.lean')
 if not path.exists():path=R/'docs/research/100bit-spend-path-20261013/lean'/(mod+'.lean')
 s=path.read_text();ns=re.search(r'^namespace (\S+)',s,re.M).group(1)
 for name in names.split():
  found=re.search(r'^(?:noncomputable )?(?:abbrev|def|structure|inductive|theorem) '+re.escape(name)+r'(?:\s|\{|\(|:)',s,re.M)
  assert found,(mod,name)
  items.append(dict(module=mod,symbol=ns+'.'+name,source=str(path.relative_to(R))))
assert len(items)==77,len(items)
(P/'BEk_review_manifest.json').write_text(json.dumps(dict(kind='77 distinct statement/trust audits; zero row-removal credit',items=items),indent=2)+'\n')
start=int(sys.argv[1]);stop=int(sys.argv[2])
for n in range(start,stop+1):
 item=items[n-21]
 src='import '+item['module']+'\n/- Distinct inherited boundary inventory; no new theorem or closure credit. -/\nset_option autoImplicit false\nset_option pp.deepTerms true\nset_option pp.fullNames true\nset_option pp.proofs false\nset_option format.width 140\n#print '+item['symbol']+'\n#print axioms '+item['symbol']+'\n'
 (R/'lean/BEk_Review.lean').write_text(src)
 print(n,item['symbol'],flush=True)
 with (P/f'BEk_{n:03}-driver.log').open('w') as log:
  result=subprocess.run([sys.executable,str(P/'BEk_compile.py'),str(n),'BEk_Review'],stdout=log,stderr=subprocess.STDOUT)
 receipt=P/f'BEk_{n:03}'/'receipt.json'
 if receipt.exists():
  r=json.loads(receipt.read_text());print({k:r[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib']},flush=True)
 if result.returncode:sys.exit(result.returncode)
