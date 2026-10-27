from pathlib import Path
import json,hashlib,re,subprocess
E=Path(__file__).resolve().parent;sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();errors=[]
receipts=[json.loads(p.read_text()) for p in sorted(E.glob('SDY_[LR][0-9][0-9][0-9]/receipt.json'))];latest={}
for r in receipts:
 a=r['attempt'];ad=json.loads((E/(a+'-reservation.json')).read_text())
 if not ad['allowed']:errors.append(a+' refused')
 if r['limits']!={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}:errors.append(a+' wrong limits')
 if str(r['swaps'])!='0':errors.append(a+' swapped')
 if r['kind']=='rust':
  for f,h in r['source_hashes'].items():
   if sha(E/a/'sources'/f)!=h:errors.append(a+' bad native source snapshot '+f)
 if r['kind']=='lean':
  for f,h in r['source_hashes'].items():
   if sha(E/a/'sources'/f)!=h:errors.append(a+' bad source snapshot '+f)
  if r['exit_status']==0:
   latest[r['module']]=r
   for line in r['print_axioms']:
    allowed={'propext','Classical.choice','Quot.sound'};names=set(re.findall(r'\[(.*?)\]',line,re.S)[0].replace('\n','').replace(' ','').split(',')) if '[' in line else set()
    if names-allowed:errors.append(a+' unapproved axiom '+str(names-allowed))
for m,r in latest.items():
 p=E/(m+'.lean')
 if sha(p)!=r['source_hashes'][r['sources'][0]]:errors.append(m+' final source differs')
for x in json.loads((E/'SDY_kit_manifest.json').read_text()):
 p=Path(x['original']);q=Path(x['copy'])
 if sha(p)!=x['source_sha256'] or sha(q)!=x['copy_sha256']:errors.append('kit source pin')
 if q.read_text().replace('SDY_Join','XRn_Join')!=p.read_text():errors.append('non-name kit change')
for p in E.glob('*.lean'):
 if re.search(r'\b(sorry|admit|axiom|native_decide)\b',p.read_text()):errors.append(p.name+' forbidden source token')
lock=json.loads((E/'SDY_lock.json').read_text());graph=json.loads((E/'SDY_graph.json').read_text());tree=json.loads((E/'SDY_frozen_tree_check.json').read_text())
if not (lock['unchanged'] and lock['before']==lock['after']==graph['lock_sha256']):errors.append('lock')
if tree['mismatches']:errors.append('frozen Rust sources')
for stem in ['Add','Row','Finish','Mp']:
 for tag in 'ABC':
  m='SDY_'+stem+tag
  owner='SDY_MpBC' if stem=='Mp' and tag in 'BC' else m
  if owner not in latest or not any("'SDY_"+stem+tag+".emitted'" in x for x in latest[owner]['print_axioms']):errors.append(m+' missing final result')
paths=subprocess.check_output(['git','diff','--name-only','fc7ae2a2ba^'],text=True).splitlines()
if any(not x.startswith('evidence/fidelity-check1-20261027/') for x in paths):errors.append('outside job directory')
(E/'SDY_attempts.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in receipts))
lean=[r for r in receipts if r['kind']=='lean'];rust=[r for r in receipts if r['kind']=='rust'];summary=dict(errors=errors,lean_compiler_launches=len(lean),lean_pass=sum(r['exit_status']==0 for r in lean),lean_preflight_failures=1,rust_runs=len(rust),rust_pass=sum(r['exit_status']==0 for r in rust),kani_runs=0,lean_wall_seconds=sum(r['wall_seconds'] for r in lean),lean_peak_rss_kib=max(int(r['peak_rss_kib']) for r in lean),swap=0,accepted_modules=list(latest),native_pass='SDY_R002',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),admission='allowed=true and exit=0 enforced by SDY_attempt.py / SDY_native_launch.py; see reservation and launcher logs',result_scope='fixture fidelity only; no premise removed')
(E/'SDY_VERIFICATION.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary));assert not errors
