#!/usr/bin/env python3
"""Assemble/check committed receipts only; never starts a build or solver."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
R=Path(__file__).resolve().parents[2]
B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/asq8-kani-20261021'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
expected='121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548'
names=['transfer_encoder_equivalence','withdrawal_encoder_equivalence','accepted_request_reencodes_exactly','request_decoder_equivalence','shipped_pipeline_normalization_equivalence','slice_array_header_comparison_model']
accepted=[]
for name in names:
 d=E/'receipts'/('kani-relocation-'+name);r=json.loads((d/'receipt.json').read_text());s=(d/'stdout.log').read_text()
 assert r['exit_status']==0 and r['swaps']==0,name
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},name
 assert '--unwinding-assertions' in r['command'] and 'VERIFICATION SUCCESSFUL' in s and '0 failures, 1 total' in s,name
 assert any(name in x for x in r['command']),name
 accepted.append(dict(name='pool_v1::pair_forest_terminal::asq8_kani::'+name,receipt=str(d.relative_to(E)/'receipt.json'),source_revision=r['source_revision'],wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps']))
lean=[]
for n in ['types-v1','external-v1','funs-v1','normalization-v2','handoff-v1']:
 d=E/'proofs'/n;r=json.loads((d/'receipt.json').read_text())
 assert r['exit_status']==0 and r['swaps']==0,n
 p=B/'lean'/(r['module'].replace('.','/')+'.lean');assert sha(p)==r['source_sha256'],p
 for line in r['print_axioms']:
  assert 'sorryAx' not in line,line
  if 'depends on axioms:' in line:
   ax=line.split('depends on axioms:',1)[1]
   assert set(re.findall(r'[A-Za-z_.]+',ax)) <= {'propext','Classical.choice','Quot.sound'},line
 lean.append(dict(module=r['module'],receipt=str(d.relative_to(E)/'receipt.json'),source_sha256=r['source_sha256'],source_revision=r['source_revision'],wall_seconds=r['wall_seconds'],peak_rss_bytes=r['peak_rss_bytes'],swaps=r['swaps'],print_axioms=r['print_axioms']))
assert (E/'pool-elf.sha256').read_text().split()[0]==expected
pool=json.loads((E/'receipts/relocation-build-pool/receipt.json').read_text());assert pool['exit_status']==0 and pool['swaps']==0
pins=json.loads((E/'artifact-pins.json').read_text())
for n in ['Types','Funs']:
 p=B/'lean/AspisR20Request'/(n+'.lean');assert sha(p)==pins[f'extraction-encoder-v6/generated/AspisR20Request/{n}.lean']['sha256'],n
identities=json.loads((E/'relocation-elf-identities.json').read_text())
assert [i['mode'] for i in identities]==['default','devnet','pool']
for i,h,n in zip(identities,['dfc2a91ab24e1ec4f57debd8f124cb4f6a3c38ba2662b7318e2e4f3b4acdde34','fb2fc048f6499a4775051d0267c76e8ca273b28f557bfd3b5fb65b2f687c8b78',expected],[1507400,1507400,605704]):
 assert i['byte_equal'] and i['sha256']==h and i['bytes']==n
 r=json.loads((E/i['receipt']).read_text())
 assert r['exit_status']==0 and r['swaps']==0
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
terminal='crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs'
original=subprocess.check_output(['git','show',f'8138bc818:{terminal}'],cwd=R)
current=(R/terminal).read_bytes()
binding=json.loads((E/'source-binding.json').read_text())
assert current.startswith(original) and binding['existing_terminal_is_exact_prefix']
assert hashlib.sha256(current[len(original):]).hexdigest()==binding['gated_addition_sha256']
reuse=json.loads((E/'relocation-lean-reuse.json').read_text())
assert reuse['reference_block_sha256']==binding['gated_addition_sha256']
assert reuse['existing_terminal_is_exact_prefix']
for entry in reuse['lean']:
 r=json.loads((E/entry['receipt']).read_text())
 assert entry['source_sha256']==r['source_sha256'] and entry['exit_status']==r['exit_status']==0
 assert entry['print_axioms']==r['print_axioms']
source=json.loads((E/'source-inputs.json').read_text())
for p,h in source.items():assert sha(R/p)==h,p
assert json.loads((E/'source-validation.json').read_text())=={'total':len(source),'mismatches':[]}
for p in [B/'lean/ASQ8Normalization.lean',B/'lean/ASQ8PoolHandoff.lean',B/'lean/AspisR20Request/FunsExternal.lean']:
 assert not re.search(r'\b(sorry|axiom|admit|native_decide|maxRecDepth|maxHeartbeats)\b', re.sub(r'/\-.*?\-/','',p.read_text(),flags=re.S)),p
m=dict(schema='focused-extractor-proof-packet-v1',job='asq8-kani-20261021',base='8138bc818',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),admitted_request_bytes=320,variants=['PrivateTransfer','Withdrawal'],P6=dict(kani_version='0.67.0',harnesses=accepted,header_model='lean/AspisR20Request/FunsExternal.lean',proof_split='Whole shipped decode/encode pipeline equivalent to fused normalizer in Kani; extracted fused normalization and exact Pool stripping composed in Lean'),lean=lean,elf_identities=identities,pool=dict(sha256=expected,size=(E/'pool-elf.size').read_text().strip(),receipt='receipts/relocation-build-pool/receipt.json',source_revision=pool['source_revision'],wall_seconds=pool['wall_seconds'],peak_rss_kib=pool['peak_rss_kib'],swaps=pool['swaps']),remaining='R20 sameSnapshot/full ASF8 account agreement and P2 runtime/CPI provenance; R9/R15 cross-transaction provenance; global P6 toolchain soundness')
if '--write' in sys.argv:
 (E/'manifest.json').write_text(json.dumps(m,indent=2)+'\n')
else:
 old=json.loads((E/'manifest.json').read_text());m['source_revision']=old['source_revision'];assert m==old,'manifest differs'
print(f'Packet verified: {len(accepted)} Kani harnesses; {len(lean)} focused Lean targets; all three frozen ELFs; original shipped line numbers preserved')
