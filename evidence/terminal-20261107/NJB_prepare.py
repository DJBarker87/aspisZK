from pathlib import Path
import json,lzma,hashlib,subprocess
E=Path(__file__).resolve().parent
L=json.loads(lzma.open(E.parent/'ledger13-20261107/NIU_LEDGER.json.xz').read())
ids=[208,209,214,215,216,217,218,219,220,223,224,225,227,228,229,231,232,233,234,235,237,242,244,245,246,247,250,251,260,261,263,268]
rows=[r for r in L['rows'] if r['row'] in {f'TX1:{n:03}' for n in ids}];assert len(rows)==32 and all(r['status']=='OPEN' and not r['owner_module'] for r in rows)
raw=json.dumps(rows,sort_keys=True,indent=1).encode();(E/'NJB_OBLIGATIONS.json.xz').write_bytes(lzma.compress(raw));(E/'NJB_OBLIGATIONS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
lookup={r['function']:r for r in L['rows']}; own={r['function'] for r in rows};done=set();order=[]
while len(done)<len(own):
 ready=[r for r in rows if r['function'] not in done and not ((set(r['canonical_callees'])&own)-done)]
 if not ready:break
 order.append([r['row'] for r in ready]);done.update(r['function'] for r in ready)
s=['# NJB terminal scope','\nTarget not yet established. Baseline NIU_LEDGER (432 CLOSED / 0 QUALIFIED / 167 OPEN). The explicit job list contains **32** occurrences, despite the heading saying 31; all 32 are retained. TX1:256 belongs to NIX_ and is excluded. Complete original obligations, caller clauses and body hashes are preserved once in NJB_OBLIGATIONS.json.xz; its uncompressed SHA is adjacent.','\nModels: FIq_Native is the retained emitted semantic/copy cohort consumed by JFy/FIx and canonical R0P.SemSource; AspisR1PublicPreparation owns semantic_public. Exact declaration availability and full signatures are to be checked before proof. The baseline supplies no named model/kernel root for 31 of these unowned rows; do not invent one. The inventory domain is the SAME Public, parsed Claims, alpha/challenges and canonical decoder outputs.','\n## Conservative bottom-up layers','\n'+'\n'.join(f'{i+1}. '+', '.join(layer) for i,layer in enumerate(order)),'\nThe inventory has over-approximated field-method alternatives. Each native body must resolve those alternatives before using a callee packet. CLOSED status below is baseline status only, not a proved caller domain.']
for r in rows:
 name=r['function'];file,fun=name.split('::',1); ns='AspisR1PublicPreparation' if r['row']=='TX1:268' else 'FIq_Native'
 decl=ns+'.'+file.split('/src/')[1].removesuffix('.rs').replace('/','.')+'.'+fun.replace('::','.')
 s += [f"\n## {r['row']} {fun}",f"Source `{file}`; frozen body SHA256 `{r['frozen_body_sha256']}`.",f"Cohort declaration to inspect: `{decl}`.",f"Original obligation SHA256 `{r['obligation_statement_hash']}`; all original clauses retained in NJB_OBLIGATIONS."]
 for c in r['canonical_callees']:
  q=lookup.get(c);status='IN NJB' if c in own else (q['status']+' '+str(q['owner_module']) if q else 'SLICE BOUNDARY / unindexed')
  s.append('- '+c+' — '+status)
(E/'NJB_SCOPE.md').write_text('\n'.join(s)+'\n')
(E/'NJB_HANDOFF.md').write_text('''# NJB handoff — stage 0

Target not yet established. Branch codex/cx-terminal-20261107. Prefix NJB_; evidence only in this directory. All 32 explicitly listed occurrences retained; no TX1:256 module will be authored. Initial scope and full obligations are pinned in NJB_SCOPE.md and NJB_OBLIGATIONS.json.xz.

Budget: 120 Kani / 100 Lean / 1 extraction. No attempts yet. One capped scope at a time; 6G high / 8G max / swap0 / tasks64, Lean -M7000, Rust optimized/offline. Admission requires exit0 AND allowed:true. Shared infrastructure unchanged; own scripts may be repaired with evidence. Host currently 98% disk used, 36G free: small private seeds only.

No CLOSED candidate, premise discharge, trust-row change, production edit or ELF rebuild claimed. Frozen3/RPx headline, L154, D188 option-A transport, privacy, two transactions and per-attempt target retained. Exact target/command/source revision/source and dependency SHA/exit/wall/RSS/swap/axioms will be retained per attempt. Native source/artifact correspondence remains qualified by the existing trust inventory. Continue bottom-up from NJB_SCOPE; consume CLOSED sibling laws read-only and discharge their complete Results at the root.
''')
print('scope: 32 rows, '+str(len(order))+' conservative dependency layers')
