from pathlib import Path
import json,hashlib,lzma,re,subprocess
E=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
attempts=[json.loads(l) for l in (E/'NND_ATTEMPTS.jsonl').read_text().splitlines()]
mods=[];roots={};receipts={}
for p in sorted(E.glob('NND_*.lean')):
 if p.stem in ['NND_COMBINED_IMPORT','NND_ProofDriver','NND_ScanDriver']:continue
 rs=[x for x in attempts if x.get('module')==p.stem and x.get('exit_status')==0 and sha(p.read_bytes()) in x.get('source_hashes',{}).values()]
 if not rs:continue
 r=rs[-1];log=E/r['attempt']/'stdout.log.xz'
 if not log.exists():continue
 out=lzma.decompress(log.read_bytes()).decode();assert 'sorryAx' not in out,p.stem
 mods.append(p.stem);receipts[p.stem]={'attempt':r['attempt'],'source_sha256':sha(p.read_bytes())}
 for n in re.findall(r"'([^']+)' (?:depends on axioms|does not depend on any axioms)",out):roots[n]=p.stem
names=list(roots);groups=[names[i:i+10] for i in range(0,len(names),10)]
modules=[list(dict.fromkeys(roots[n] for n in g)) for g in groups]
(E/'NND_AUDIT_ROOTS.json').write_text(json.dumps({'groups':groups,'owners':roots,'scope':'current successful NND own roots ONLY'},indent=1)+'\n')
(E/'NND_AUDIT_MODULES.json').write_text(json.dumps(modules,indent=1)+'\n')
(E/'NND_CURRENT_MODULES.json').write_text(json.dumps(receipts,indent=1)+'\n')
(E/'NND_COMBINED_IMPORT.lean').write_text('import NLX_COMBINED_IMPORT\n'+'\n'.join('import '+m for m in mods)+'\nset_option autoImplicit false\n')
p=E/'NND_reuse'/'NND_audit_support';p.mkdir(exist_ok=True)
pins={}
for stem in ['NFA_WALKER','NFA_MemoryLimit']:
 path='evidence/ledger24-20261110/NLX_L005/sources/NLX_native/'+stem+'.c'
 raw=subprocess.check_output(['git','show','HEAD:'+path]);(p/(stem+'.c')).write_bytes(raw);pins[stem]={'provenance':path,'sha256':sha(raw)}
(E/'NND_AUDIT_C_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
print(json.dumps({'modules':len(mods),'roots':len(roots),'groups':len(groups)}))
