"""Bounded immutable published-source analysis only; never invokes Lean."""
import hashlib,json,pathlib,re,resource,time
start=time.monotonic()
E=pathlib.Path(__file__).resolve().parents[2]/'evidence/port34raw-20261025'
P=pathlib.Path('/private/tmp/Port34RAW-20261025');P.mkdir(exist_ok=True)
def pin(p):
 return dict(path=str(p),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest())
src=E/'Port34RAW_reused-reused-reference358-Query31SourceCalls.lean.txt'
s=src.read_text();lines=s.splitlines()
anchor='        (∃ first rest, pairs = first :: rest ∧ first.state = absorbed.state) ∧\n'
a=s.index('theorem queries_success_with_digest_pairs_full');b=s.index(' := by',a)
after=s[a:b];assert after.count(anchor.rstrip('\n'))==1
before=after.replace(anchor,'');assert before!=after
pairs=[dict(line=i+1,text=l.strip(),pair=int(re.search(r'let pair(\d)',l)[1])) for i,l in enumerate(lines) if re.match(r'  let pair\d :',l)]
assert len(pairs)==8 and [x['pair'] for x in pairs]==list(range(8))
for x in pairs:
 x['hcall_references']=re.findall(r'hcall\d+',x['text'])
 x['state']=re.search(r'⟨([^,]+),',x['text'])[1]
assert pairs[0]['state']=='self1.state'
witness=[dict(line=i+1,text=l.strip()) for i,l in enumerate(lines) if 'let pairs :' in l or 'refine ⟨pairs, hcall1' in l or 'exact ⟨pair0, [pair1' in l]
binds=[dict(line=i+1,text=l.strip()) for i,l in enumerate(lines) if ' := bind_success ' in l or ' := pair_bind_success ' in l]
# These are source binders, not metadata/Expr positions; no actual data was exported.
r=dict(status='SOURCE-ONLY finite inventory; NOT actual Expr inventory',source=pin(src),source_association='immutable published reference, not raw body identity',pairs=pairs,witness_tail=witness,successful_execution_bind_decompositions=binds,raw_exports=0,actual_Expr_positions='UNAVAILABLE360 failed before IO',theorem_checked=False,lean_calls=0,wall_seconds=time.monotonic()-start,peak_rss_bytes=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,swaps=resource.getrusage(resource.RUSAGE_SELF).ru_nswap)
assert r['peak_rss_bytes']<512*1024**2
(E/'Port34RAW_source-structural.json').write_text(json.dumps(r,indent=2)+'\n')
intro='''# Proposed finite execution-tail repair — UNCOMPILED

Actual360 exports are unavailable: ordinary run_cmd failed before IO. These
complete before/after statements use immutable published notation and the
REUSED358 actual mismatch; they are NOT a new actual raw-type export. No
actual Expr positions/constructor spine were inspected. No theorem checked.

BEFORE: actual358 weaker statement reconstructed in published notation:

```lean
'''
tail='''
```

No premise/binder/carrier/outcome changes. H/B/D/self/after/row/payload/out/h
and every old absorb/decode/after/length/stateChain/materializedOutputs conjunct
are unchanged. The addition is solely the initial pair anchor conclusion.
Do not derive it from arbitrary list length/stateChain, introduce a new premise,
weaken Bridge, or use proof irrelevance between different propositions.

Proposed actual repair, contingent on an actual future value export: locate the
successful source execution's final five Exists.intro witnesses (absorbed,
blocks, advances, selected, pairs) and right-associated And.intro chain. Preserve
all preceding execution eliminations and old proof components. After length,
replace old And.intro hchain hmaterial with
And.intro (Exists.intro pair0 (Exists.intro [pair1,...,pair7]
  (And.intro rfl rfl))) (And.intro hchain hmaterial), using actual typed terms,
not this pseudocode. Corresponding predicate/type parameters and enclosing
eliminator motives must be strengthened throughout the same execution proof;
merely changing the outer introduction is insufficient when motives mention
its result. All original names, levels, binders and dependencies are retained.

Published source establishes the intended finite construction shape: self1
comes from the first successful absorb bind (hcall1); pair0.state is self1.state
by the displayed DigestPair constructor; pairs is [pair0,...,pair7]. Thus the
finite anchor witness is
`⟨pair0, [pair1,pair2,pair3,pair4,pair5,pair6,pair7], rfl, rfl⟩`.
Source-structural.json lists exact published line numbers, states, hcall fields
and execution bind decompositions. This does not certify the actual weaker
value has those lets or that the proposed term type-checks. No generic wrapper
over the weaker theorem supplies the missing fact.

The unchanged dependent Bridge retains H/M/Cv/L/B/D/p/pubInput/root/length/
self/after/row/payload/out/h, all original output conjuncts and oracle-address
conclusions. Its complete published statement/body is retained beside this
note. REUSED358 application diagnostic expects the anchor in the Calls result.
Actual Bridge TYPE/VALUE export and same-context normal check remain blocked.

Future SOURCE review alternative: remain entirely in Kernel.Environment,
replay normally checked exact-name declarations, build a new enclosing Expr /
Declaration, and normally check with Core.getMaxHeartbeats. Do not transport
kernel-only metadata into elaboration. No private constructors, manual records,
unchecked insertion, trust imports or rename/cast allowed. This is not executed.
'''
text=intro+before+'\n```\n\nAFTER: proposed stronger conclusion only:\n\n```lean\n'+after+tail
(E/'Port34RAW_BEFORE-AFTER-UNCOMPILED.md').write_text(text)
(P/'Port34RAW_source-structural.json').write_text(json.dumps(r,indent=2)+'\n')
print(dict(pairs=len(pairs),bind_decompositions=len(binds),peak_rss_bytes=r['peak_rss_bytes'],wall_seconds=r['wall_seconds']))
