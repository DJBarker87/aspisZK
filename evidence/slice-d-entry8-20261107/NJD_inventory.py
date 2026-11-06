from pathlib import Path
import subprocess,json,lzma,hashlib,re
E=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
ledger=json.loads(lzma.decompress((E.parent/'ledger13-20261107/NIU_LEDGER.json.xz').read_bytes()))
ids=['TX1:330','TX1:333','TX1:344','TX1:345','TX1:328','TX2:213','TX2:221','TX2:240','TX2:241','TX2:216','TX2:217','TX2:218','TX2:233','TX2:234','TX2:242','TX1:329','TX2:212']
byid={r['row']:r for r in ledger['rows']}; sources={};rows=[];pins={}
for rid in ids:
 r=byid[rid];assert r['status']=='OPEN';path,name=r['function'].split('::',1)
 if path not in sources:
  raw=subprocess.check_output(['git','show',rev+':'+path]);sources[path]=raw.decode();h=sha(raw);q=E/(f'NJD_FROZEN_{Path(path).name}.xz');q.write_bytes(lzma.compress(raw));pins[path]=dict(sha256=h,bytes=len(raw),archive=q.name)
 s=sources[path];m=re.search(r'\bfn\s+'+re.escape(name)+r'\s*(?:<[^\n]*>)?\s*\(',s);assert m,(rid,name)
 start=s.index('{',m.end());depth=1;i=start+1
 while depth:
  if s[i]=='{':depth+=1
  if s[i]=='}':depth-=1
  i+=1
 body=s[start+1:i-1];calls=[]
 for cm in re.finditer(r'([A-Za-z_][\w]*(?:::[A-Za-z_][\w]*)*)\s*\(',body):
  n=cm[1]
  if n in ['if','match','while','for','Some','Ok','Err']:continue
  dep=1;k=cm.end()
  while dep and k<len(body):
   if body[k]=='(':dep+=1
   if body[k]==')':dep-=1
   k+=1
  matches=[z for z in ledger['rows'] if z['function'].endswith('::'+n) or z['function'].endswith('::'+n.split('::')[-1])]
  selected=[z for z in matches if z['function'] in r['canonical_callees']]
  known=[z for z in selected if z['status']=='CLOSED']
  item=dict(order=len(calls)+1,callee=n,arguments=body[cm.end():k-1],line=s[:start+1+cm.start()].count('\n')+1)
  if known:item.update(law_class='CLOSED row (domain and full packet still to instantiate)',law_rows=[z['row'] for z in known],roots=[v for z in known for v in z['root_owners']])
  elif selected:item.update(law_class='MISSING CLOSED callee packet',law_rows=[z['row'] for z in selected])
  elif n in ['len','is_empty','first','get','copied','checked_add','map_err','new_from_array','to_bytes','as_ref','semantic_public','common','nullifier','tag']:item.update(law_class='P7 candidate: exact emitted specialization/domain/frame must be matched; not admitted by name')
  elif n in ['snapshot']:item.update(law_class='CLOSED snapshot + NIV_SnapshotSequence producer; native ABI/call cut remains OPEN')
  elif n in ['Clock::get']:item.update(law_class='RuntimeClockSlotBinding only binds returned slot; error/ABI cut remains OPEN')
  elif n in ['program::set_return_data']:item.update(law_class='RuntimeReturnDataClear for empty argument; native exact slice/effects cut remains OPEN')
  elif n in ['try_borrow_data','try_borrow_mut_data']:item.update(law_class='SDK borrow law requires pinned P7/retained S2TrustedSdkBorrow matching; RuntimeEntrypointAdmission alone insufficient')
  else:item.update(law_class='MISSING exact specialization/packet/frame lemma; cannot assume')
  calls.append(item)
 rows.append(dict(row=rid,function=r['function'],frozen_function_sha256=sha(s[m.start():i].encode()),start_line=s[:m.start()].count('\n')+1,calls=calls,canonical_callees=r['canonical_callees'],status='OPEN'))
x=dict(frozen_revision=rev,baseline='NIU_LEDGER',baseline_sha256=sha(lzma.decompress((E.parent/'ledger13-20261107/NIU_LEDGER.json.xz').read_bytes())),source_pins=pins,rows=rows,method='Source-ordered call inventory cross-checked against canonical emitted slots; library candidates are NOT credited laws')
(E/'NJD_INVOCATION.json').write_text(json.dumps(x,indent=1)+'\n')
d=['# NJD invocation inventory','', 'All 17 rows remain OPEN. Frozen call arguments below are verbatim source expressions; the emitted canonical body inspection is NJD_INSPECT.txt. NIV_L022 supplies entry/process emission; owned bodies use canonical AdapterRwModel. Slot correction: digest/error are op43/op44; decoders master/checkpoint/lane are op48/op49/op50. SDK stages are wrappers, not declarations AdapterRw.r1_pool_adapter.owned.stage1/stage2.', '', 'A CLOSED row listed here identifies the law source, not a discharge. Each caller must instantiate its complete Result, same arguments and full frame under (aq). Unmatched primitive/SDK calls are exact missing-law entries, not P7 assumptions. Runtime entry admission supplies only its seven fields and does not prove SDK implementation laws. No candidate child success or RuntimeCpiReadonlyEntry7 is used.','']
for r in rows:
 d+=['## '+r['row']+' '+r['function'].split('::')[-1],'']
 for c in r['calls']:
  a=' '.join(c['arguments'].split()); d.append(f"{c['order']}. L{c['line']} `{c['callee']}({a})`: {c['law_class']}"+((' ['+', '.join(c['law_rows'])+']') if c.get('law_rows') else ''))
 d+=['','Canonical call dependencies: '+', '.join('`'+c+'`' for c in r['canonical_callees'])+'.','']
(E/'NJD_INVOCATION.md').write_text('\n'.join(d)+'\n')
print(json.dumps(dict(rows=len(rows),calls=sum(len(r['calls']) for r in rows),source_files=len(pins))))
