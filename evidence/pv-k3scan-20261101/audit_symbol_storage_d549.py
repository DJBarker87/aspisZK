from pathlib import Path
import json,lzma
E=Path(__file__).resolve().parent;out=[]
for folder in sorted((E/'host').glob('K792[0-9][0-9]')):
 if not(folder/'receipt.json').exists():continue
 files=list(folder.glob('symbols-*.json.xz'));items=[]
 for p in files:
  d=json.loads(lzma.decompress(p.read_bytes()))
  for part in d:
   for name,s in part.get('symbolTable',{}).items():
    if s.get('isStateVar')and s.get('isStaticLifetime'):
     items.append({'name':name,'pretty_type':s.get('prettyType'),'location':s.get('location'),'generated_const':s.get('prettyType','').startswith('const '),'tool_builtin':name in ['VoidUnit','__CPROVER_dead_object','__CPROVER_memory']or name.startswith('__CPROVER_')})
 out.append({'run':folder.name,'symbol_files':len(files),'static_state_items':items,'review_candidates':[s for s in items if not s['generated_const']and not s['tool_builtin']]})
d={'method':'Read retained per-run CBMC symbol JSON; no compilation or solver. This is a storage inventory, not an independent source/macro-closure theorem. Kani generated immutable allocated constants and CBMC builtins are distinguished from candidates for review. Source/stub provenance remains authoritative.','runs':out}
(E/'D549-SYMBOL-STORAGE.json').write_text(json.dumps(d,indent=2)+'\n');print({'runs':len(out),'with_symbols':sum(bool(x['symbol_files'])for x in out),'review_candidates':[(x['run'],[(s['name'],s['pretty_type'])for s in x['review_candidates']])for x in out if x['review_candidates']]})
