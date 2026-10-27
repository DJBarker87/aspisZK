from pathlib import Path
import json,subprocess,re,hashlib
P=Path(__file__).resolve().parent;cs=json.loads((P/'checks.json').read_text());pins=json.loads((P/'pins.json').read_text())['revisions']
# Fourteen additional inspections cover newly merged/supporting statements rather
# than modifying the byte-identical checks rejected by the duplicate guard.
spec=[('cblib',n) for n in ['PV_CBL_PadContentSource','PV_CBL_ByteWordsSource','PV_CBL_SoftByteSource','PV_CBL_FinalizeSoftValue','PV_CBL_FinalizeSoftTotal','PV_CBL_DigestBytesList','PV_CBL_DigestUpdateSource','PV_CBL_DigestSoftTotal']]+[('research',n) for n in ['PV_OptB_Charged','PV_OptB_OffBad','PV_OptB_OffBadJoin','PV_OptB_FirstFailureOffBad','PV_Canon_AuditFinal','PV_Canon_ArrayDomain']]
for ref,n in spec:
 m='R1Z.'+n;path='docs/research/v8-r0-zk-20261009/lean/R1Z/'+n+'.lean';q=subprocess.run(['git','show',pins[ref]+':'+path],capture_output=True);assert q.returncode==0,(n,q.stderr)
 s=q.stdout.decode();ns=re.findall(r'^namespace\s+(\S+)',s,re.M);ns=ns[-1] if ns else ''
 names=re.findall(r'^#print axioms\s+(\S+)',s,re.M);assert names,n
 fq=list(dict.fromkeys(x if x.startswith('R1Z.') else ns+'.'+x for x in names))[-2:]
 text='import '+m+'\nset_option pp.proofs false\n'+''.join('#check '+x+'\n#print '+x+'\n#print axioms '+x+'\n' for x in fq)
 name='PV_Ledger_Recount5_Support_'+n;out=P/'helpers'/(name+'.lean');out.write_text(text)
 cs.append(dict(module=name,source=str(out.relative_to(P)),sha256=hashlib.sha256(text.encode()).hexdigest(),items=[[m,x] for x in fq],pinned_ref=ref,pinned_path=path,pinned_sha256=hashlib.sha256(q.stdout).hexdigest()))
(P/'checks.json').write_text(json.dumps(cs,indent=2)+'\n');print(len(cs),'planned targets; actual Lean limit 20')
