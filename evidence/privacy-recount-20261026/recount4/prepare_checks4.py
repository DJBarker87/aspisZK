from pathlib import Path
import subprocess,json,re,hashlib
P=Path(__file__).resolve().parent
specs=[('Headline','research','PrivacyR1HeadlineDeployedReal'),('Dictionary','rw','ProverRwFullExternalFuns'),('RwModel','rw','ProverRw21ModelInstance'),('RwCompression','rw','ProverRw19CanonicalAuditRefinement'),('Callbacks','cb','PV_CB_Op229Source'),('Cb3','cb3','PV_CB3_Op51Arbitrary'),('Cbmid','cbmid','PV_CBM_CallbackBundle'),('Library','cblib','PV_CBL_CallbackBundle'),('PathTypes','cblib','PV_CBL_PathTypes'),('PathSource','cblib','PV_CBL_PathBorrowSource'),('Op223','op223','PV_Op223_Source'),('V164','op223','PV_Op223_V164'),('SourcePremises','research','PV_Src_NativePremises'),('PublicCorr','research','PV_Src_RootSourceEquation'),('Trust','runjoin','PV_RunJoin_TrustItems'),('RunJoin','runjoin','PV_RunJoin_TrustEndpoint'),('Records','runjoin','PV_RunJoin_RecordedTransfer'),('OptionB','optb','PV_OptB_Endpoint'),('Inversion','research','PV_Inv_GuardCoupling'),('Wire','join','PV_Join_Wire_FinalAuditA')]
pins=json.loads((P/'pins.json').read_text())['revisions'];checks=[]
for label,ref,module in specs:
 path='docs/research/v8-r0-zk-20261009/lean/R1Z/'+module+'.lean'
 p=subprocess.run(['git','show',pins[ref]+':'+path],capture_output=True)
 if p.returncode:
  path='docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/'+module+'.lean';p=subprocess.run(['git','show',pins[ref]+':'+path],capture_output=True)
 assert p.returncode==0,(module,p.stderr)
 s=p.stdout.decode();names=re.findall(r'^#(?:print(?: axioms)?|check)\s+([^\s]+)',s,re.M)
 # Existing explicit commands identify declarations in their namespace.
 namespaces=re.findall(r'^namespace\s+(\S+)',s,re.M);ns=namespaces[-1] if namespaces else ''
 if not names:
  names=re.findall(r'^(?:@\[[^\n]*\]\s*)?(?:noncomputable\s+)?(?:theorem|def|abbrev|structure|class)\s+([^\s(:{]+)',s,re.M)[-3:]
 fq=list(dict.fromkeys(n if n.startswith('R1Z.') else ns+'.'+n for n in names))[:5]
 if label=='Dictionary':fq=['R1Z.ProverRwFull.ExternalFuns']
 if label=='OptionB':fq=['R1Z.PV_OptB_Endpoint.privacy_headline_deployed_B','R1Z.PV_OptB_Endpoint.realTestB','R1Z.PV_OptB_Endpoint.idealTestSB']
 if label=='Wire':fq=['R1Z.PV_Join_Wire_Caller.refinement_of_data']
 if label=='Library':fq+=['R1Z.PV_CBL_CallbackBundle.op28_source']
 text='import R1Z.'+module+'\nset_option pp.proofs false\n'+''.join('#check '+n+'\n#print '+n+'\n#print axioms '+n+'\n' for n in fq)
 name='PV_Ledger_Recount4_'+label;out=P/'helpers'/(name+'.lean');out.parent.mkdir(exist_ok=True);out.write_text(text)
 checks.append(dict(module=name,source=str(out.relative_to(P)),sha256=hashlib.sha256(text.encode()).hexdigest(),items=[[module,n] for n in fq],pinned_ref=ref,pinned_path=path,pinned_sha256=hashlib.sha256(p.stdout).hexdigest()))
(P/'checks.json').write_text(json.dumps(checks,indent=2)+'\n');print([(x['module'],x['items']) for x in checks])
