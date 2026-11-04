from pathlib import Path
import json,re,hashlib
E=Path('evidence/slice-d-checkpoint-20261104')
receipts=[]
for p in sorted(E.glob('NGC_L[0-9][0-9][0-9]/receipt.json')):
 r=json.loads(p.read_text())
 if r['exit_status']==0 and r.get('print_axioms'):receipts.append((p,r))
roots={}
for p,r in receipts:
 for a in r['print_axioms']:
  m=re.match("'([^']+)' depends on axioms: \\[(.*)\\]",a)
  if m and ('NGC_' in m[1] or m[1]=='AspisR1.RPx_Deployed.deployed'):
   assert 'sorryAx' not in m[2]
   roots[m[1]]=str(p)
modules=['NGC_ByteWriters','NGC_Initialization','NGC_FinishContents','NGC_ValueBridge','NGC_WriterDomain','NGC_DigestBridge','NGC_CheckpointBridge','NGC_AppendFrame','NGC_InitialInvariant','NGC_FillInduction','NGC_ReferenceValues']
text='import RPx_Deployed\nimport NFT_STAGE2_IMPORT\nimport NFU_STAGE2_IMPORT\n'+''.join('import '+m+'\n' for m in modules)+''.join('#print axioms '+n+'\n' for n in roots)
(E/'NGC_COMBINED_IMPORT.lean').write_text(text)
(E/'NGC_AUDIT_ROOTS.json').write_text(json.dumps(roots,indent=1)+'\n')
s=(E/'NGC_Driver.lean').read_text(); start=s.index('    else\n      (#[`NGC_COMBINED_IMPORT]');end=s.index('\n  let env',start)
groups=[list(roots)[i:i+10] for i in range(0,len(roots),10)]
replace=''
for i,g in enumerate(groups):
 replace+='    else if mode == "proof'+str(i)+'" then\n      (#[`NGC_COMBINED_IMPORT],#['+','.join('`'+n for n in g)+'])\n'
replace+='    else\n      (#[`NGC_COMBINED_IMPORT],#[])'
s=s[:start]+replace+s[end:];(E/'NGC_ProofDriver.lean').write_text(s)
# Extend expected manifest solely from exact committed/own source headers.
p=E/'NGC_EXPECTED_IMPORTS.jsonl';rows={r['module']:r for r in map(json.loads,p.read_text().splitlines())};pins=[]
for p in list(E.glob('NGC_*.lean'))+list(E.glob('NGC_*Ref/*.lean')):
 n=str(p.relative_to(E).with_suffix('')).replace('/','.')
 imports=list(dict.fromkeys(['Init']+[n for l in p.read_text().splitlines() if l.startswith('import ') for n in l.split()[1:] if n!='all']))
 rows[n]=dict(module=n,imports=imports);pins.append(dict(module=n,path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),imports=imports))
(E/'NGC_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(r)+'\n'for r in rows.values()))
(E/'NGC_FINAL_IMPORT_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
batch='''from pathlib import Path\nimport subprocess,json,hashlib,lzma,sys,time,os\nb=Path.cwd();out=b/'NGC_final_audit';out.mkdir(exist_ok=True)\nt='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0';binary=b/'NGC_native/NGC_ProofDriver'\ncmd=[t+'/bin/lake','env','leanc','-O3','-rdynamic','-o',str(binary),'NGC_native/NGC_ProofDriver.c','NGC_native/NGC_WALKER.c','NGC_native/NGC_MemoryLimit.c']\nr=subprocess.run(cmd,capture_output=True,text=True);(out/'link.log').write_text(r.stdout+r.stderr);assert r.returncode==0\nresults=[]\nfor mode in MODES:\n started=time.monotonic();r=subprocess.run([str(binary),mode],capture_output=True,text=True,timeout=120)\n (out/(mode+'.log')).write_text(r.stdout+r.stderr);results.append(dict(mode=mode,exit_status=r.returncode,wall_seconds=time.monotonic()-started))\n print(mode,r.returncode,r.stdout[-900:],flush=True)\n if mode=='fixtures':assert r.returncode!=0 and r.stdout.count('NEP_RAW_')>=8,r.stdout\n else:assert r.returncode==0,r.stdout+r.stderr\n for p in b.glob('NEP_'+mode+'_*_REACHABLE.txt'):\n  raw=p.read_bytes();(out/(p.name+'.xz')).write_bytes(lzma.compress(raw,preset=6));(out/(p.name+'.sha256')).write_text(hashlib.sha256(raw).hexdigest()+'  '+p.name+'\\n');p.unlink()\n(out/'results.json').write_text(json.dumps(results,indent=1)+'\\n')\n'''.replace('MODES',repr(['fixtures']+['proof'+str(i) for i in range(len(groups))]+['scan']))
(E/'NGC_final_audit_batch.py').write_text(batch)
print(len(roots),'roots',len(groups),'groups')
