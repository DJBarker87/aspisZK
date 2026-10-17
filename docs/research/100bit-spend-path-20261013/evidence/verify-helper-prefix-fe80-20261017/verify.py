#!/usr/bin/env python3
"""Read/hash-only accepted artifact, precise receipt and statement binding audit."""
from pathlib import Path
import hashlib,json,tarfile,re,importlib.util
E=Path(__file__).resolve().parent;B=E.parents[1];R=B.parents[2];sha=lambda b:hashlib.sha256(b).hexdigest();m=json.loads((E/'manifest.json').read_text());a=E/'verify-helper-prefix-accepted.tar.gz';assert sha(a.read_bytes())==m['archive_sha256']
with tarfile.open(a) as t:
 sums=json.load(t.extractfile('SHA256SUMS.json'));assert len(t.getmembers())==len(sums)+1==m['members'];files={n:t.extractfile(n).read() for n in sums}
 for n,b in files.items():assert sha(b)==sums[n],n
 records={Path(n).stem:json.loads(b) for n,b in files.items() if n.startswith('proof/successful-targets/')}
 assert len(records)==23==m['successful_targets'];count=0
 for name,d in records.items():
  assert d['exit_status']==0 and d['axioms']['passed'] and d['process_swaps']==0 and d['cgroup_swap_current']=='0',name
  assert d['limits']=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0'}
  source=files['proof/sources/'+name.replace('.','/')+'.lean'];assert sha(source)==d['key']['source_sha256'],name
  for suf,v in d['objects'].items():assert sha(files['proof/objects/'+name.replace('.','/')+suf])==v['sha256']
  for dep,pin in d['key']['imports'].items():
   if dep in records:
    rd=records[dep];assert pin['receipt_key']==sha(json.dumps(rd['key'],sort_keys=True).encode()),(name,dep)
    assert pin['objects']==rd['objects'],(name,dep)
  for report in d['axioms']['reports']:assert set(report['axioms'])<={'propext','Classical.choice','Quot.sound'};count+=1
  assert not re.search(rb'^import .*FunsExternal',source,re.M),name
 assert count==98==m['axiom_reports']
 llbc=json.loads(files['prefix-extraction/VerifyHelperPrefix.llbc']);assert not llbc.get('has_errors',False)
 kit=json.loads(files['prefix-extraction/input/source-pins.json']);assert kit['kit_files']['lib.rs']==sha(files['prefix-extraction/input/lib.rs'])
 K=B/'tools/verify-helper-prefix-kit';norm=json.loads((K/'input-normalized/source-pins.json').read_text());assert (K/'input-normalized/lib.rs').read_bytes()==files['prefix-extraction/input/lib.rs'];assert norm['base52_cuts']==kit['base_cuts'] and norm['cuts']==kit['cuts']
 # Replay only the exact identifier substitutions and binder additions.
 spec=importlib.util.spec_from_file_location('inventory',B/'tools/j1-integrated-declaration-repin.py');m2=importlib.util.module_from_spec(spec);spec.loader.exec_module(m2)
 O=B/'lean/bridge-verify-prefix-fe80-20261017';audit=json.loads((O/'binding-audit.json').read_text());raw=files['prefix-extraction/generated/AspisR1PublicPreparation/Funs.lean'];assert sha(raw)==audit['raw_funs_sha256'];chunks=m2.lean_chunks(raw);mapping=audit['identifier_map'];pattern=re.compile('|'.join(re.escape(n)+r'(?![A-Za-z0-9_.])' for n in sorted(mapping,key=len,reverse=True)))
 model=(O/'ExtractedVerifyPrefixModel.lean').read_bytes();assert sha(model)==audit['model_sha256']
 for item in audit['exact_body_audits']:
  name=item['declaration'];src=chunks[name];assert sha(m2.canonical(m2.lean_tokens(src)))==item['source_token_sha256'];body=pattern.sub(lambda z:mapping[z[0]],src)
  if item['binder_addition']:body=body.replace('def '+mapping[name]+'\n','def '+mapping[name]+item['binder_addition']+'\n',1)
  assert sha(body.encode())==item['model_sha256'] and body.encode() in model
 for n in ['ExtractedPrefixParseCore','ExtractedVerifyPrefixModel','ExtractedVerifyPrefixReachability','ExtractedFirstHelperBinding']:
  assert (O/(n+'.lean')).read_bytes()==files['proof/sources/'+n+'.lean']
 print('PASS388 members;23 coherent current targets;98 standard-only reports; exact2body substitutions; frozen58cuts; failures excluded from acceptance')
