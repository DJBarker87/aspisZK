from pathlib import Path
import json,hashlib,lzma,re
E=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
obj=lambda p:json.loads(Path(p).read_text())
standard={'propext','Classical.choice','Quot.sound'}
def results(a):
 s=(E/a/'stdout.log').read_text();assert 'NEP_FAILURE' not in s
 return [json.loads(l.split('NEP_RESULT ',1)[1]) for l in s.splitlines() if l.startswith('NEP_RESULT ')]
def receipt(a):
 r=obj(E/a/'receipt.json');assert r['exit_status']==0
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert int(r['swaps'])==0
 ad=obj(E/(a+'-admission.json'));assert ad['exit']==0 and ad['reservation']['allowed'] is True
 for n,h in r['source_hashes'].items():assert sha(E/a/'sources'/n)==h
 return r
walker=(E/'NFE_WALKER.lean.txt').read_bytes();assert walker==(E.parent/'axaudit2-20261102/NEP_WALKER.lean').read_bytes()==(E.parent/'slice-q-mul4-20261104/NFA_WALKER.lean').read_bytes()
roots=obj(E/'NFE_DRIVER_ROOTS.json');assert roots['walker_sha256']==hashlib.sha256(walker).hexdigest()
# Check the scanner block is exactly NER's active-declaration and canonical-import scan.
ner=(E.parent/'coherent-20261102/NER_FinalDriverV2.lean').read_text();scanner=ner[ner.index('namespace NER'):ner.index('\nopen Lean Elab Command',ner.index('namespace NER'))]
assert scanner in (E/'NFE_Driver.lean').read_text() and hashlib.sha256(scanner.encode()).hexdigest()==roots['scanner_sha256']
fixture=results('NFE_L058');assert len(fixture)==8
assert fixture==obj(E.parent/'slice-q-mul5-20261104/NFC_AUDIT.json')['fixtures']
for x in fixture:assert x['equal'] and x['collect_axioms']==x['walked_axioms']
assert all(len(x['walked_axioms'])==1 and x['walked_axioms'][0].startswith('NEP_Planted.') for x in fixture[:4])
assert all(x['walked_axioms']==[] for x in fixture[4:])
rs=[];pins=set()
for i,g in enumerate(roots['groups']):
 a=f'NFE_L{60+i:03}';r=receipt(a);xs=results(a);assert [x['root'] for x in xs]==g
 pins.add(obj(E/a/'NFE_Driver_BINARY_PIN.json')['sha256'])
 for x in xs:
  assert x['equal'] and x['walked_axioms']==x['collect_axioms'] and set(x['walked_axioms'])<=standard
  p=E/('NEP_proof'+str(i)+'_'+x['root']+'_REACHABLE.txt');raw=lzma.decompress(Path(str(p)+'.xz').read_bytes())
  h=hashlib.sha256(raw).hexdigest();assert Path(str(p)+'.sha256').read_text().strip()==h
  assert len(raw.decode().splitlines())==x['reachable_constants'] and x['root'] in raw.decode().splitlines()
  rs.append(dict(attempt=a,reachable_sha256=h,**x))
assert len(pins)==1 and len(rs)==len(roots['roots']) and {x['root'] for x in rs}==set(roots['roots'])
scan=[json.loads(l) for l in (E/'NFE_LOADED_scan.jsonl').read_text().splitlines()]
assert all(x['imports_match'] and not x['dangling'] for x in scan)
assert 'NFE_SCAN_ZERO_DANGLING' in (E/'NFE_L059/stdout.log').read_text()
assert {'RPx_Deployed','NFE_CombinedFinal','NFE_NFC_MainPacket','NFE_NFC_WrapperPacket'}<={x['module'] for x in scan}
for i in range(1,101):
 r=receipt(f'NFE_L{i:03}')
 if isinstance(r['print_axioms'],list):
  for l in r['print_axioms']:
   if 'does not depend on any axioms' in l:continue
   axioms=re.search(r'axioms: \[([^]]*)\]',l);assert axioms
   assert {x.strip() for x in axioms[1].split(',') if x.strip()}<=standard
result=dict(status='PASS_COMBINED_HEADLINE_FOREST',headline='AspisR1.RPx_Deployed.deployed',walker_unchanged=True,walker_sha256=roots['walker_sha256'],scanner_unchanged=True,scanner_sha256=roots['scanner_sha256'],driver_diff_sha256=sha(E/'NFE_DRIVER.diff'),driver_binary_sha256=next(iter(pins)),fixture_attempt='NFE_L058',fixtures=fixture,roots=len(rs),groups=len(roots['groups']),results=rs,standard_axioms_only=True,raw_graphs_equal_collectAxioms=True,zero_unresolved_constants=True,incoherence_scan=dict(attempt='NFE_L059',modules=len(scan),declarations=sum(x['declarations'] for x in scan),edges=sum(x['edges'] for x in scan),dangling=0,import_mismatches=0,output_sha256=sha(E/'NFE_LOADED_scan.jsonl')),budget=dict(lean_audit_support_used=100,lean_limit=100,kani_used=0,kani_limit=40,extraction_used=0,extraction_limit=5),security_target_established=False)
(E/'NFE_AUDIT.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS:',len(rs),'roots;',len(scan),'coherent loaded modules; all100 scopes validated')
