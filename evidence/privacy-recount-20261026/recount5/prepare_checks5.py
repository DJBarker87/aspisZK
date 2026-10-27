from pathlib import Path
import subprocess,json,re,hashlib
P=Path(__file__).resolve().parent;pins=json.loads((P/'pins.json').read_text())['revisions']
specs=[('Headline','research','R1Z.PrivacyR1HeadlineDeployedReal'),('Dictionary','rw','R1Z.ProverRwFullExternalFuns'),('RwModel','rw','R1Z.ProverRw21ModelInstance'),('V164','rw','R1Z.PV_Op223_V164'),('Op223','rw','R1Z.PV_Op223_Source'),('Callbacks','cb','R1Z.PV_CB_Op229Source'),('Cb3','cb3','R1Z.PV_CB3_Op51Arbitrary'),('Cbmid','cbmid','R1Z.PV_CBM_CallbackBundle'),('Append','cblib','R1Z.PV_CBL_AppendBundle'),('SoftDigest','cblib','R1Z.PV_CBL_DigestSoftSource'),('Op134','op134','R1Z.PV_Op134_AuditClosure'),('SourcePremises','research','R1Z.PV_Src_NativePremises'),('PublicCorr','research','R1Z.PV_Src_RootSourceEquation'),('Trust','runjoin','R1Z.PV_RunJoin_TrustItems'),('RunJoin','runjoin','R1Z.PV_RunJoin_TrustEndpoint'),('OptionB','research','R1Z.PV_OptB_Endpoint'),('Inversion','research','R1Z.PV_Inv_GuardCoupling'),('Wire','join','R1Z.PV_Join_Wire_FinalAuditA'),('Sampler','l2b','PV_L2B_SamplerLaw'),('Guards','l2b','PV_L2B_Guards')]
checks=[]
for label,ref,m in specs:
 path='docs/research/v8-r0-zk-20261009/lean/'+m.replace('.','/')+'.lean'
 q=subprocess.run(['git','show',pins[ref]+':'+path],capture_output=True)
 if q.returncode:
  path='docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/'+m.split('.')[-1]+'.lean';q=subprocess.run(['git','show',pins[ref]+':'+path],capture_output=True)
 assert q.returncode==0,(m,q.stderr)
 s=q.stdout.decode();names=re.findall(r'^#(?:print(?: axioms)?|check)\s+([^\s]+)',s,re.M)
 ns=re.findall(r'^namespace\s+(\S+)',s,re.M);ns=ns[-1] if ns else ''
 if not names:names=re.findall(r'^(?:@\[[^\n]*\]\s*)?(?:noncomputable\s+)?(?:theorem|def|abbrev|structure|class)\s+([^\s(:{]+)',s,re.M)[-3:]
 fq=list(dict.fromkeys(n if n.startswith(('R1Z.','PV_L2B_')) else ns+'.'+n for n in names))[:5]
 if label=='Dictionary':fq=['R1Z.ProverRwFull.ExternalFuns']
 if label=='Wire':fq=['R1Z.PV_Join_Wire_Caller.refinement_of_data']
 text='import '+m+'\nset_option pp.proofs false\n'+''.join('#check '+n+'\n#print '+n+'\n#print axioms '+n+'\n' for n in fq)
 name='PV_Ledger_Recount5_'+label;out=P/'helpers'/(name+'.lean');out.parent.mkdir(exist_ok=True);out.write_text(text)
 checks.append(dict(module=name,source=str(out.relative_to(P)),sha256=hashlib.sha256(text.encode()).hexdigest(),import_module=m,items=[[m,n] for n in fq],pinned_ref=ref,pinned_path=path,pinned_sha256=hashlib.sha256(q.stdout).hexdigest()))
(P/'checks.json').write_text(json.dumps(checks,indent=2)+'\n');print(len(checks),'helpers prepared')
