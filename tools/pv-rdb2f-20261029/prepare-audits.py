from pathlib import Path
import re,json,hashlib,subprocess
P=Path('docs/research/v8-r0-zk-20261009/lean/R1Z');E=Path('evidence/pv-rdb2f-20261029');files=sorted(p for p in P.glob('PV_RDB2F_*.lean')if not any(x in p.stem for x in ['Audit','Replay']));theorems=[];decls=[];modules=[]
for p in files:
 s=p.read_text();namespace=re.search(r'^namespace (\S+)',s,re.M)[1];names=[namespace+'.'+m for m in re.findall(r'^theorem (\w+)',s,re.M)];theorems+=names;decls+=names
 for n in re.findall(r'^(?:structure|def|abbrev) (\w+)',s,re.M):decls.append(namespace+'.'+n)
 modules.append(dict(module='R1Z.'+p.stem,path=str(p),source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),source_blob=subprocess.check_output(['git','rev-parse','HEAD:'+str(p)],text=True).strip(),imports=re.findall(r'^import (\S+)',s,re.M)))
imports=''.join('import '+r['module']+'\n'for r in modules)
(P/'PV_RDB2F_StatementAudit.lean').write_text(imports+'\n'+''.join('#print '+n+'\n'for n in decls))
(P/'PV_RDB2F_AxiomsAudit.lean').write_text(imports+'\n'+''.join('#print axioms '+n+'\n'for n in decls))
(P/'PV_RDB2F_FocusedReplay.lean').write_text(imports+'\n'+''.join('#print axioms '+n+'\n'for n in theorems))
(E/'frozen-proof-manifest.json').write_text(json.dumps(dict(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),modules=modules,theorems=theorems,named_declarations=decls,audits=[63397,63398,63399]),indent=2)+'\n')
print(len(modules),'modules;',len(theorems),'theorems;',len(decls),'declarations')
