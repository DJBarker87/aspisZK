"""Produce conservative review queues, preserving every source/line match."""
import json,re,collections,hashlib,subprocess
from pathlib import Path
out=Path('evidence/pv-d188-20261027');x=json.loads((out/'inventory.json').read_text());decls=[]
for e in x['emissions']:
 p=e['file'];t=Path(p).read_text();ds=list(re.finditer(r'^def\s+([^\s({:]+)',t,re.M))
 for i,d in enumerate(ds):
  b=t[d.start():ds[i+1].start() if i+1<len(ds) else len(t)]
  if not re.search(r'index_mut|iter_mut|chunks(?:_exact)?_mut|get_mut|next_back|Slice.update|Array.update|Vec.update',b):continue
  line=t.count('\n',0,d.start())+1;backs=set(re.findall(r'\b\w*(?:_back|restore)\w*\b',b));unused=[n for n in backs if len(re.findall(r'\b'+re.escape(n)+r'\b',b))==1]
  sites=[dict(line=line+b.count('\n',0,m.start()),text=m[0]) for m in re.finditer(r'let\s*\(([^)]+)\)\s*(?:←|:=)\s*([^\n]+)',b) if re.search(r'(^|,)\s*_\s*(,|$)',m[1]) and re.search(r'_mut|IterMut|next|back|restore',m[2])]
  decls.append(dict(file=p,declaration=d[1],line=line,body_sha256=hashlib.sha256(b.encode()).hexdigest(),unused_back_names=unused,wildcard_mut_sites=sites,source=next((r for r in reversed(e['sources']) if r['emission_line']<=line),None)))
(out/'mutable-declarations.json').write_text(json.dumps(decls,indent=2)+'\n')
md=['# Emission inventory','',f"Base `{x['revision']}`. {len(x['emissions'])} files; {sum(e['file'] in x['roots'] for e in x['emissions'])} are root-family files. Source annotations are claims of provenance, not independently proved associations. Duplicate cohorts are retained. Source-annotated hand ports are included conservatively.",'','| Emitted/ported module | Claimed Rust functions (source locations in inventory.json) |','|---|---|']
for e in x['emissions']:
 refs=list(dict.fromkeys(r['claim'].split('Name pattern:')[0].strip() for r in e['sources']))
 md.append('| `'+e['file']+'` | '+('; '.join('`'+r.replace('|','/').replace('`','')+'`' for r in refs) or 'No embedded Rust location; generated header only (type/support module).')+' |')
(out/'INVENTORY.md').write_text('\n'.join(md)+'\n')
md=['# Mutable declaration review queue','', 'Each row links a syntactic mutation candidate to its nearest embedded Rust source annotation. Original pin lines may predate current source; current source sites are separately enumerated in rust-mutable-sites.json. This table is exposure, not a claim of divergence. Functions parametrized by external dictionaries do not provide closed native executions without an actual dictionary instance.','', '| Emission and line | Declaration | Claimed Rust source |','|---|---|---|']
for d in decls:
 r=d['source'];loc=(r['rust']+':'+str(r['rust_start'])) if r else 'unannotated/inherited'
 md.append(f"| `{d['file']}:{d['line']}` | `{d['declaration']}` | `{loc}` |")
(out/'MUTABLE-DECLARATIONS.md').write_text('\n'.join(md)+'\n')
# Preserve sibling-branch observations without importing/cherry-picking its code.
branch='codex/pv-batch2-20261027';rev=subprocess.check_output(['git','rev-parse',branch],text=True).strip();paths=['crates/aspis-r1-cost-probe/src/host_sampler.rs','crates/aspis-r1-cost-probe/src/host_weights.rs','docs/research/v8-r0-zk-20261009/lean/R1Z/PV_B2_RawSamplerFuns.lean','docs/research/v8-r0-zk-20261009/lean/R1Z/PV_B2_WeightsFuns.lean'];obs=[]
for p in paths:
 data=subprocess.check_output(['git','show',rev+':'+p]);t=data.decode();obs.append(dict(path=p,sha256=hashlib.sha256(data).hexdigest(),matches=[dict(line=i,text=l.strip()) for i,l in enumerate(t.splitlines(),1) if re.search(r'low_base_p_digits|add_small_base_p|iter_mut|index_mut|Array.update|quotient\[|digits\[',l)]))
(out/'batch2-readonly-observation.json').write_text(json.dumps(dict(branch=branch,revision=rev,part_of_audited_base=False,observations=obs),indent=2)+'\n')
print('modules',len(x['emissions']),'mutable declarations',len(decls))

# Pair each lexical emission site with all current source writes in its claimed span.
writes=json.loads((out/'rust-mutable-sites.json').read_text());by={}
for w in writes:by.setdefault(w['file'],[]).append(w)
ms=json.loads((out/'static-matches.json').read_text())
for m in ms:
 r=m['source'];m['current_rust_sites_in_annotated_span']=[w for w in by.get(r['rust'],[]) if r['rust_start']<=w['line']<=r['rust_end']] if r else []
 m['association']='embedded source-span claim; current writes listed, not a proof of source revision identity'
(out/'paired-static-matches.json').write_text(json.dumps(ms,indent=2)+'\n')
