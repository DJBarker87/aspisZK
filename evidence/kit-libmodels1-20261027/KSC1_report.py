"""Render the complete assigned-row table; no source/model mutation."""
from pathlib import Path
import json,collections
E=Path(__file__).resolve().parent;x=json.loads((E/'KSC1_assignment.json').read_text());rows=x['rows']
D='https://doc.rust-lang.org/1.94.1/std/'
notes={
'MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter':('UNDETERMINED','array borrowed IntoIterator','P7 to_slice/from_slice substrate only. Whole continuation must restore a full-length slice and all yielded mutable items; no arbitrary-context invariant proved. KSC1.P7.restored_array; R002 writeback probe.'),
'Slice.Insts.CoreCmpPartialEqArray.eq':('FAITHFUL','slice/array PartialEq','KSC1.P7.slice_array_eq (L004): exact equality to pinned P7 core.slice.cmp.PartialEqSlice.eq, with arbitrary comparator, lengths and Result branches. P7 trust retained; not independent Rust comparator refinement.'),
'Slice.Insts.CoreCmpPartialEqArray.ne':('FAITHFUL','slice/array PartialEq','KSC1.P7.slice_array_ne_p7 (L009): exact equality to pinned P7 ne, monadic De Morgan proof preserves errors/divergence and short-circuit. P7 trust retained.'),
'XRn_Join_enumerateNext':('UNDETERMINED','enumerate next ABI','P7 next supplies element writeback; wrapper preserves supplied item via Prod.snd. Missing valid mutable-reference carrier/continuation proof and reached usize counter bound (checked overflow differs from wrapping profiles); ignores supplied Iterator dictionary. R002 covers basic enumeration only.'),
'XRn_Join_enumerateRestored':('UNDETERMINED','enumerate borrow ABI','Constructor returns iter/count0 and projects iter on restoration. Missing arbitrary legal continuation/element-writeback law and reachability of the dictionary/borrow carrier; native R002 is a fixture.'),
'XRn_Join_fromFnState':('UNDETERMINED','from_fn state ABI','L006 proves exact state-threaded indexed traversal, including fail/div. Rust external-capture restoration and partial-initialisation/closure Drop effects are not represented/proved. R002 observes final16, ascending indices and panic cleanup, not an arbitrary-effect refinement.'),
'XRn_Join_intoIter':('UNDETERMINED','array mutable IntoIterator ABI','P7 Array.from_slice silently returns original array when restored length differs. L004 proves writeback only at full length. Must prove every legal restore chain supplies that full slice and all mutations; no unrestricted law follows from native R002.'),
'XRn_Join_iterator':('UNDETERMINED','IterMut Iterator dictionary','Its next is XRn_Join_next, which drops the P7 item-restoration continuation. A borrowed T carrier/callback law justifying this projection is missing; no mutation-complete association.'),
'XRn_Join_mapArray':('UNDETERMINED','pure carrier-map helper','Pure List.map conversion, not Rust array::map/FnMut. No error, callback-state or Drop carrier is present; use only as a proved carrier adapter, not a standard-library refinement.'),
'XRn_Join_next':('UNDETERMINED','IterMut next ABI projection','L004 next_projection is EXACTLY projection of P7 next and discards its writeback continuation. No connection from arbitrary yielded mutable-reference updates to original slice. Projection equality is not mutable next fidelity.'),
'XRn_Join_nextBackPair':('UNFAITHFUL','IterMut next_back ABI','L002: after P7 next on [7], state i=1; this returns Some7. Native R002 returns None. Replace underlying mutable next_back reset index0 with current s.i, then prove/retain full restoration chain. No product-path reachability claim.'),
'XRn_Join_revRestored':('UNDETERMINED','rev borrow ABI','Constructor/projection lens alone is not arbitrary continuation fidelity; consumer uses refuted next_back. Prove corrected next_back, legal borrow restoration and fixed dictionary association before use. R002 covers basic reversed writes.'),
'XRn_Join_reverseNext':('UNFAITHFUL','Rev next ABI','L010 reverse_repeats_spent: Rev around i=1/[7] returns Some7 instead of None (R002 native). Delegates to index-reset mutable next_back. Fix that dependency; preserve/retain both returned back continuations. L010 also checks singleton changed-item writeback and empty case.'),
'alloc.vec.Vec.is_empty':('FAITHFUL','Vec::is_empty','KSC1.vec_is_empty (L011) proves ok(length=0) for arbitrary element type/allocator/vector. Shared query, no allocation/callback/writeback or panic branch. Rust1.94.1 vec/mod.rs:2957-2959; native R002 tests zero/nonzero.'),
'core.array.fromFnList':('UNDETERMINED','from_fn traversal helper','No P7 definition at this name. L006 indexed_eq proves all loop iterations/state/error propagation against an indexed traversal. Fuel/index helper accepts states not reachable from N/0; no complete Rust mutable capture, drop or panic-effect relation. R002 covers empty/success/panic.'),
'core.array.from_fn':('UNDETERMINED','array::from_fn','No P7 same-name definition. Traversal threads F internally but drops final F from API; arbitrary external mutable-capture restoration and panic drop are unassociated. R002 final external state16/drops2 alone cannot prove this missing relation.'),
'core.array.mapListFnMut':('UNDETERMINED','array::map traversal helper','No P7 same-name definition. Output subtype proves length and recursion threads F; no relation to Rust ownership of non-Copy input/output, partial mapped Drop, or external capture restoration. R002 success-order fixture only for this helper.'),
'core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.collect':('UNDETERMINED','Map::collect','P7 collect.default supplies delegation but local Map.next loop has no proved arbitrary FromIterator/callback effect/ref-ownership law. R002 empty/success/panic prefix only. No whole collection or heap-effect proof.'),
'core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.fold':('UNDETERMINED','Rev::fold','No P7 same-name body. Local loop consumes next_back and threads callback state but exports only accumulator; mutable-item/captured-reference writeback and panic/drop effect law missing. R002 reverse-order/empty fixtures.'),
'core.iter.traits.iterator.Iterator.all.default':('UNDETERMINED','Iterator::all','No P7 same-name body. Loop has right empty/continue/stop control flow, but drops final F and exports no borrow/effect relation; arbitrary callbacks and item restoration unproved. R002 empty/all-true/false-with-remainder/panic-prefix branches.')
}
# Precise obstruction classes for the inventory rows that are not std externals.
for r in rows:
 n=r['name'];k=r.get('kernel_name',n)
 if n in notes:v,kind,note=notes[n]
 elif n in ['XRn_Join_mpow','XRn_Join_qpow']:
  v,kind='UNFAITHFUL','Aspis power stand-in (mislabelled library)';note='Retained KSA failure: exponent2 at base2 yields1, square is4. Not a std/core item. Correct with raw emitted power/fixed-chain inverse association; KSA_FINDING failure matrix and KSA_L002, not newly replayed.'
 elif r['kind'] in ['abbrev','structure','inductive']:
  v,kind='UNDETERMINED','Aspis carrier/type (mislabelled library)';note=f'{k} is a representation/alias, not an external std function. Missing a source/adopted-carrier association for its uses; P7 cannot establish Aspis nominal-carrier identity.'
 elif 'Carriers' in r['file'] or n in ['XRn_Join_nativeAfter','XRn_Join_nativeLive','XRn_Join_nativePublic','XRn_Join_nativeQ','XRn_Join_nativeTransition','XRn_Join_oldAfter','XRn_Join_oldLive','XRn_Join_oldPublic','XRn_Join_oldTransition','XRn_Join_oldChallenges','XRn_Join_releaseQ','XRn_Join_newError']:
  v,kind='UNDETERMINED','Aspis carrier adapter (mislabelled library)';note=f'{k} converts/projections Aspis fields. Roundtrip alone is not source association, adopted installation or full effects/error transport. No Rust std item or P7 body corresponds to this nominal adapter.'
 elif n in ['actual','boundaries','cachedClaim','sampling','chosen','copyUnit']:
  v,kind='UNDETERMINED','Aspis dictionary/helper (mislabelled library)';note=f'{k} assembles a dictionary/selects a result or defines a test Copy instance. Missing emitted/adopted dictionary association, not a Rust std fidelity obligation. Do not infer closure from projection/slot equalities.'
 else:
  v,kind='UNDETERMINED','Aspis arithmetic/byte/source helper (mislabelled library)';note=f'{k} is an Aspis helper rather than a Rust std/core external. No unique documented std function exists for this body; source/body or explicit adapter association remains required. No P7 citation or passing fixture can replace that association.'
 r.update(verdict=v,classification=kind,evidence_or_obstruction=note)
 assert r['verdict'] in ['FAITHFUL','UNFAITHFUL','UNDETERMINED']
ranked=sorted(rows,key=lambda r:(-r['kernel_witness_count'],-r['raw_qualified_occurrences'],r['alphabetical_row']))
(E/'KSC1_verdicts.json').write_text(json.dumps(dict(counts=dict(collections.Counter(r['verdict'] for r in rows)),ordering='descending retained kernel-witness count, then exact qualified-name raw occurrences, then alphabetical assignment row; static prioritisation only',rows=ranked),indent=2)+'\n')
header='''
## Per-model verdicts (complete assigned half)

Ordering uses retained KSA kernel witness counts, then qualified raw-emission
occurrences, as the available static use evidence. These are first-unresolved-node
witnesses, **not exhaustive kernel fan-in or measured reached-path frequency**.
No adopted-run frequency certificate exists in this packet; that exact ordering
requirement is UNDETERMINED. Alphabetical assignment numbers preserve the split.
The raw short-name substring counts in the assignment are not usage evidence.

FAITHFUL for equality/inequality means exact equality to the **resolved P7 base**;
P7 trust, comparator/ABI admission and caller reference validity remain. The
Vec verdict is against the documented shared-query operation. All other scoped
positive lemmas are recorded without upgrading the full operation's verdict.
The two retained power failures are not new library defects. Full source hashes,
kernel names, locations, static counts and obstructions are in KSC1_verdicts.json.

| Assignment row | Declaration (qualified where inventory supplied it) | Use witnesses | Kind | Verdict | Evidence / exact obstruction |
|---|---|---:|---|---|---|
'''
lines=[header]
for r in ranked:lines.append(f"| {r['alphabetical_row']} | `{r.get('kernel_name',r['name'])}` ({Path(r['file']).name}:{r['line']}) | {r['kernel_witness_count']} | {r['classification']} | **{r['verdict']}** | {r['evidence_or_obstruction']} |")
(E/'KSC1_table.md').write_text('\n'.join(lines)+'\n')
