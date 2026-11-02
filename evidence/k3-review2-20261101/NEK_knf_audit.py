"""Expand the complete pinned standalone KNF module closure; no proof replay."""
from NEK_scan import *
A=read_json(ROOT/'evidence/k3-audit-20261030/NEH_APPLICABILITY.json');out=[]
for row in A['receipts']:
 if '/KNF_K' not in row['receipt']:continue
 r=read_json(ROOT/row['receipt']);sources={}
 for n,v in row['matched_sources'].items():
  p=ROOT/v['source'];b=p.read_bytes();assert sha(b)==v['sha256'];sources[n]=b.decode()
 assert len(sources)==3
 assert all(not re.search(r'\bstatic\b|\b(?:UnsafeCell|Atomic[A-Za-z0-9_]*|thread_local)\b',t) for t in sources.values())
 macros=sorted({m for t in sources.values() for m in re.findall(r'\b([A-Za-z_][\w:]*)!\s*[\[({]',t)})
 # Qualified alloc::vec! is the same pinned standard allocation macro; it
 # introduces a local Vec, no writable static. Keep all copy/K-2 qualifications.
 assert set(macros)<={'alloc::vec','assert','assert_eq','debug_assert','assert_ne','panic','unreachable','kani::cover'}
 out.append(dict(receipt=row['receipt'],harness=row['harness'],status='UNAFFECTED_COMPLETE_STANDALONE_CLOSURE',sources={n:sha(t.encode()) for n,t in sources.items()},macro_expansion_review=macros,module_paths='KNF_harness.rs -> KNF_field.rs -> KNF_wide_exact.rs, all three receipt-pinned',retained='all original domains, K-1/K-2 and native/model transport qualifications; no new native credit'))
(E/'NEK_KNF_SOURCE_AUDIT.json').write_text(json.dumps(out,indent=2)+'\n');print('PASS',len(out),'standalone receipts, no Kani replay')
