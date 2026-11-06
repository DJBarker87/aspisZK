from pathlib import Path
import json,lzma,subprocess,hashlib,re
E=Path(__file__).resolve().parent;H=lambda b:hashlib.sha256(b).hexdigest()
J=lambda p:json.loads(lzma.decompress(p.read_bytes())if p.suffix=='.xz'else p.read_bytes())
b=J(E.parent/'ledger20-20261109/NKW_LEDGER.json.xz');by={r['row']:r for r in b['rows']};rows=[]
for folder,pre in [('tx2-resume2-20261109','NKU'),('row-bridges-20261109','NKY')]:
 for f in J(E.parent/folder/(pre+'_CLOSED.json'))['rows']:
  r=by[f['row']];assert r['status']=='OPEN' and r['function']==f['function']
  file,name=r['function'].split('::',1);text=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+file]);t=text.decode();a=re.search(r'fn '+re.escape(name)+r'(?:<|\()',t).start();p=t.index('{',a);q=p+1;d=1
  while d:d+=(t[q]=='{')-(t[q]=='}');q+=1
  braces=H(t[p:q].encode());assert braces==r['frozen_body_sha256']==f.get('baseline_frozen_body_sha256',f.get('frozen_body_sha256'))
  if 'baseline_obligation_statement_hash'in f:assert r['obligation_statement_hash']==f['baseline_obligation_statement_hash']
  rows.append(dict(row=r['row'],file=file,source_sha256=H(text),body_sha256=braces,function_text=t[a:q],same_frozen_function=True))
# Revalidate retained emission/body transport and (bc) pattern directly, read-only.
p=E.parent/'row-bridges-20261109';x=J(p/'NKY_LITERAL_INPUT.json');emission=subprocess.check_output(['git','show','HEAD:'+x['path']]);assert H(emission)==x['sha256']and x['excerpt']in emission.decode()
s=x['excerpt'];a=s.index('def\n  pool_');z=s.index('/-- [aspis_statement::',a)
body=s[a:z].replace('pool_v1.pair_forest_semantic_terminal.append_levels_packed_selector_tensor_loop.body','body').replace('pool_v1.pair_forest_semantic_terminal.append_level_packed_selector_tensor','child').replace('aspis_core.field.QM31','FIq_Native.field.QM31').replace('aspis_core.field.M31','U32').replace('def\n  body','def body (child : U64 → Usize → NJX_DigestCohort.D → NJX_DigestCohort.O → FIv_NativeArithmetic.NQ → Result NKY_LevelCarrier.Pair)')
assert body in(p/'NKY_LevelsLiteral.lean').read_text()
f=next(r for r in rows if r['row']=='TX1:235')['function_text'];assert f.endswith('    (local0, local12)\n}')and 'return 'not in f and '?'not in f
freeze='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';pool='b936275465600469312d1f058cdc91ea2a11f3dc'
for rev,paths in [(freeze,['crates','programs/r1-cost-probe','Cargo.lock']),(pool,['programs/aspis-pool'])]:
 r=subprocess.run(['git','diff','--quiet',rev,'--',*paths]);assert r.returncode==0
(E/'NLG_SOURCE_REVIEW.json').write_text(json.dumps(dict(status='PASS',rows=rows,literal_body_transport_exact=True,retained_emission_sha256=x['sha256'],bc='tuple tail, no explicit post-loop return or question mark; unaffected',source_identity_exit=0,verifier_revision=freeze,pool_revision=pool,pool_pin='e0e49c344d35575116c0359450315ea4334bfb03006551727f67c04a8cfe09dc',historical_pool_pin='121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548',elf_rebuild_trigger=False),indent=1)+'\n')
print('Four frozen bodies, literal emission, post-loop shape and release identities PASS')
