from pathlib import Path
import re,json,math,hashlib
E=Path(__file__).resolve().parent
mods=['NFW_Bind','NFW_Transcript','NFW_TranscriptDomain','NFW_PreparedControl','NFW_PreparedResults','NFW_PreparedFields','NFW_StoredLayout','NFW_StoredWindows','NFW_QueryEntry','NFW_QueryStart','NFW_PreparedPort','NFW_QueryResume','NFW_ReferenceEq','NFW_SampledDomains','NFW_FoldedPayload','NFW_Invert','NFW_PreparedCalls','NFW_ScalarRho','NFW_PreparedProducer','NFW_PrepareQuery','NFW_ErrorReferenceEq']
roots=[]
for m in mods:
 s=(E/(m+'.lean')).read_text();ns=re.search(r'^namespace (\S+)',s,re.M).group(1)
 roots += [n if '.' in n else ns+'.'+n for n in re.findall(r'^#print axioms (\S+)',s,re.M)]
assert len(roots)==60 and len(set(roots))==60
(E/'NFW_STAGE2_ROOTS.json').write_text(json.dumps(roots,indent=1)+'\n')
(E/'NFW_STAGE2_IMPORT.lean').write_text('import NFW_COMBINED_IMPORT\n'+''.join('import '+m+'\n' for m in mods))
s=(E/'NFW_ProofDriver.lean').read_text();start=s.index('    if mode == "proof0"');stop=s.index('    else if mode == "fixtures"',start)
parts=[]
for i in range(math.ceil(len(roots)/8)):
 parts.append(('    if' if i==0 else '    else if')+f' mode == "stage{i}" then\n      (#[`NFW_STAGE2_IMPORT], #['+', '.join('`'+r for r in roots[i*8:(i+1)*8])+'])\n')
s=s[:start]+''.join(parts)+s[stop:];(E/'NFW_Stage2Driver.lean').write_text(s)
s=(E/'NFW_final_audit_batch.py').read_text().replace('NFW_final_audit','NFW_stage2_audit').replace('NFW_ProofDriver','NFW_Stage2Driver').replace("[f'proof{i}' for i in range(4)]","[f'stage{i}' for i in range(8)]")
(E/'NFW_stage2_audit_batch.py').write_text(s)
p=E/'NFW_run.py';s=p.read_text().replace("command=['python3','NFW_stage2_audit_batch.py']","command=['python3','NFW_stage2_audit_batch.py',a+'.json']");p.write_text(s)
(E/'NFW_STAGE2_AUDIT_BUILD.json').write_text(json.dumps(dict(roots=len(roots),walker_source_sha256=hashlib.sha256((E/'NFW_WALKER_SOURCE.lean.txt').read_bytes()).hexdigest(),driver='Same audited raw walker/support; only module/root selection changed',new_modules=mods,old_powers_roots_reused=30,fixtures=8),indent=1)+'\n')
