from pathlib import Path
import json,time,subprocess,re,sys,lzma,hashlib,base64
B=Path.cwd();mode=sys.argv[1];E=B/'NJL_audit'/mode;E.mkdir(parents=True,exist_ok=True)
command=['NJL_native/'+('NJL_Driver'if mode=='scan'else'NJL_ProofDriver'),mode]
start=time.monotonic()
with (E/'stdout.log').open('w')as f:r=subprocess.run(['/usr/bin/time','-v','-o',str(E/'time.log'),*command],stdout=f,stderr=subprocess.STDOUT)
s=(E/'stdout.log').read_text();t=(E/'time.log').read_text()
def metric(k):
 m=re.search(re.escape(k)+r':\s*(.*)',t);return m[1]if m else None
results=[json.loads(l[11:])for l in s.splitlines()if l.startswith('NEP_RESULT ')];axioms=[l for l in s.splitlines()if'depends on axioms'in l or'does not depend on any axioms'in l]
attempt={'fixtures':'NJL_L047','proof0':'NJL_L048','proof1':'NJL_L049','scan':'NJL_L050'}[mode]
config=json.loads((B/(attempt+'.json')).read_text())
row=dict(target=mode,source_revision=config['source_revision'],scope_attempt=attempt,library_pins='see '+attempt+'/receipt.json deps_fingerprint',command=command,exit_status=r.returncode,wall_seconds=time.monotonic()-start,peak_rss_kib=metric('Maximum resident set size (kbytes)'),swaps=metric('Swaps'),results=results,print_axioms=axioms)
if mode=='fixtures':
 expected=[['NEP_Planted.matchAx'],['NEP_Planted.privateAx'],['NEP_Planted.proofAx'],['NEP_Planted.auxAx'],[],[],[],[]];row['fixture_pass']=len(results)==8 and all(x['equal']and x['walked_axioms']==want for x,want in zip(results,expected));assert row['fixture_pass']
elif mode.startswith('proof'):
 allowed={'propext','Quot.sound','Classical.choice'};row['standard_only']=len(results)>0 and all(x['equal']and set(x['walked_axioms'])<=allowed for x in results);assert row['standard_only']
if mode=='scan':
 p=B/'NJL_LOADED_scan.jsonl';raw=p.read_bytes();rows=[json.loads(l)for l in raw.splitlines()];row.update(modules=len(rows),dangling=sum(len(x['dangling'])for x in rows),duplicate_owners=sum(len(x['duplicate_owners'])for x in rows),import_mismatch=sum(not x['imports_match']for x in rows));(E/'scan.jsonl.xz.b64.txt').write_text(base64.b64encode(lzma.compress(raw)).decode());(E/'scan.jsonl.sha256').write_text(hashlib.sha256(raw).hexdigest());assert not(row['dangling']or row['duplicate_owners']or row['import_mismatch'])
(E/'receipt.json').write_text(json.dumps(row,indent=1));print(json.dumps({k:v for k,v in row.items()if k not in ['results','print_axioms']}));sys.exit(r.returncode)
