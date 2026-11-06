from pathlib import Path
import json,lzma,hashlib,difflib,re
E=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
idx=json.loads((E/'NJN_INPUTS.json').read_text());objects=idx['objects'];patches=[];seen=set();pairs=[]
for a in sorted(idx['attempts']):
 if not a.startswith('NJN_K'):continue
 files={n:lzma.decompress((E/objects[h]['path']).read_bytes()).decode() for n,h in idx['attempts'][a].items() if n.startswith('NIJ_src/')}
 own={n:t for n,t in files.items() if '/NJN_' in n and n.endswith('.rs')}
 for n,t in own.items():
  h=sha(t.encode())
  if (n,h) not in seen:
   seen.add((n,h));patches.append(''.join(difflib.unified_diff([],t.splitlines(True),fromfile='/dev/null',tofile=n)))
  pairs.append(dict(attempt=a,path=n,sha256=h))
 for n,t in files.items():
  if '/NJN_' in n or not n.endswith('.rs'):continue
  own_suffix=''.join(re.findall(r'\n#\[cfg\(kani\)\]\n#\[path="NJN_[^"\n]+"\]\nmod NJN_[^;\n]+;\n',t))
  if not own_suffix:continue
  h=sha(own_suffix.encode())
  if (n,h) not in seen:
   seen.add((n,h));base=t
   for suffix in re.findall(r'\n#\[cfg\(kani\)\]\n#\[path="NJN_[^"\n]+"\]\nmod NJN_[^;\n]+;\n',own_suffix):base=base.replace(suffix,'')
   patches.append(''.join(difflib.unified_diff(base.splitlines(True),t.splitlines(True),fromfile=n,tofile=n)))
raw='\n'.join(patches).encode();(E/'NJN_native_packets.patch.xz').write_bytes(lzma.compress(raw));(E/'NJN_native_packets.patch.sha256').write_text(sha(raw)+'\n')
(E/'NJN_NATIVE_PATCHES.json').write_text(json.dumps(dict(note='Versioned own cfg-only harness patches; exact source input per attempt is in NJN_INPUTS',patch='NJN_native_packets.patch.xz',raw_sha256=sha(raw),pairs=pairs),indent=1)+'\n')
# Frozen authoritative baseline is inspected, never rewritten.
p=E.parent/'ledger14-20261108/NJK_LEDGER.json.xz';raw=lzma.decompress(p.read_bytes());expected=(p.parent/'NJK_LEDGER.json.sha256').read_text().split()[0];assert sha(raw)==expected
(E/'NJN_LEDGER_DELTA.json').write_text(json.dumps(dict(baseline=str(p),baseline_raw_sha256=expected,before=dict(CLOSED=438,QUALIFIED=0,OPEN=161),after=dict(CLOSED=438,QUALIFIED=0,OPEN=161),promotions=[],law_certificates_completed=0,target_established=False,reason='Supporting SDK models/native preflights do not complete extracted-reference or ABI gates'),indent=1)+'\n')
print('NJN source patches and zero ledger delta packaged')
