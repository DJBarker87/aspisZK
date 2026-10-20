#!/usr/bin/env python3
"""Validate pinned original client regions, emitted bodies, and selected proofs."""
from pathlib import Path
import hashlib,json,re,subprocess,sys,argparse,time,resource
started=time.monotonic()
ap=argparse.ArgumentParser();ap.add_argument('--source-only',action='store_true');ap.add_argument('--receipt-prefix',default='canonical-clients-final-');a=ap.parse_args()
tool=Path(__file__).resolve().parent;area=tool.parents[1];ev=area/'evidence/cu-equivalence-20261019';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for script in ['extract-canonical-dot-clients.py','extract-canonical-dot-partials.py','emit-canonical-dot-clients.py','emit-canonical-dot-partials.py']:
 subprocess.run([sys.executable,str(tool/script),'--check'],check=True,stdout=subprocess.DEVNULL)
modules=['AspisR1CanonicalDotClients/'+x for x in ['Types','FunsExternal','Funs']]+['AspisR1CanonicalDotPartials/'+x for x in ['Types','FunsExternal','Funs']]+['CuSavingsCanonicalDotClientInputs','CuSavingsCanonicalDotPartials','CuSavingsCanonicalDotClientFactors','CuSavingsCanonicalDotClients','CuSavingsCanonicalDotArray','CuSavingsCanonicalDotPartialsCanonical']
entries=[]; records={}; objects={}
for i,module in enumerate(modules,1):
 p=area/'lean'/Path(module+'.lean');raw=p.read_text();assert not re.search(r'(?m)^\s*(?:axiom|opaque)\s|\bsorry\b|\badmit\b',raw),module
 item=dict(module=module,source_sha256=sha(p),declarations=re.findall(r'(?m)^(?:def|theorem|abbrev)\s+([\w.]+)',raw))
 if not a.source_only:
  d=ev/(a.receipt_prefix+str(i));r=json.loads((d/'receipt.json').read_text());assert r['exit_status']==0,module;assert r['source_sha256']==sha(p),module;assert 'sorryAx'not in r['print_axioms_output'],module
  audits=re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",r['print_axioms_output']);assert audits,module
  for decl,axs in audits:assert set(filter(None,re.sub(r'\s+','',axs).split(',')))<={'propext','Classical.choice','Quot.sound'},(decl,axs)
  records[module.replace('/','.')]=r;objects[module.replace('/','.')]=r['object_sha256']
  item.update(receipt=str(d.relative_to(area)),wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],process_swaps=r['process_swaps'],source_revision=r['source_revision'],command=r.get('command'),features=r.get('features'),print_axioms=r['print_axioms_output'])
 entries.append(item)
if not a.source_only:
 for module,r in records.items():
  for imported in r['direct_imports']:
   if imported['module']in objects:assert imported['sha256']==objects[imported['module']],(module,'incoherent_selected_import',imported)
result=dict(coherent_selected_imports=not a.source_only,status='SOURCE_PASS'if a.source_only else'PASS',candidate='e58b87665233febecc1b1a75c506eac1a8b72e00',parent='d11f9b2fcbddf68fd1ffec297f987de0aa95a6c0',targets=entries,scope='Actual final enumerate, exact shared16-row+outer4 partial builder and high4 source clients. Decoder/finish values establish canonicality; no arbitrary input canonicality premise remains on caller_context or final_equivalence. Original source fission is inverse audited and ordinary Result-bind factoring, not a new interpreter or arithmetic premise.',source_boundary='Inherited audited Rust→Charon→Aeneas source extraction and existing source-runtime implementations; production Rust unchanged.')
result['audit']=dict(command=[sys.executable,*sys.argv],source_revision=subprocess.check_output(['git','-C',str(tool.parents[4]),'rev-parse','HEAD'],text=True).strip(),features=[],exit_status=0,wall_seconds=time.monotonic()-started,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss//1024,process_swaps=resource.getrusage(resource.RUSAGE_SELF).ru_nswap,print_axioms='N/A: source/receipt audit; exact Lean axiom output retained in targets.')
if not a.source_only:(ev/'CANONICAL-DOT-CLIENTS-FINAL.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(status=result['status'],targets=len(entries),new_axioms=False)))
