from pathlib import Path
import json,re,collections,hashlib
E=Path(__file__).resolve().parent;R=E.parent.parent
assignment=json.loads((E/'KSC2_assignment.json').read_text()); rows=assignment['assigned']
raw=(R/'evidence/extraction-assoc2-20261027/XRj_L013/sources/XRj_generated/XRh_Release/Funs.lean').read_text()
tokens=collections.Counter(re.findall(r'[A-Za-z_][A-Za-z_0-9.]*',raw))
graph={}
for a in ['KSA_L023','KSA_L024']:
 for line in (E.parent/'kit-audit1-20261027'/a/'stdout.log').read_text().splitlines():
  if line.startswith('KSA_DEP '):
   x=json.loads(line[8:]);graph[x['name']]=x
wanted={r['kernel_name'] for r in rows}
consumers=collections.defaultdict(set)
for name,x in graph.items():
 if not x['theorem']:continue
 todo=[name];seen=set()
 while todo:
  n=todo.pop()
  if n in seen:continue
  seen.add(n)
  if n in wanted:consumers[n].add(name)
  if n in graph:todo.extend(graph[n]['refs'])
base='https://doc.rust-lang.org/1.94.1/std/'
iterator=base+'iter/trait.Iterator.html#method.'
p7={
'core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.collect':('range_collect','collect.default (IteratorRange step) out'),
'core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.rev':('range_rev','rev.default'),
'core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.enumerate':('range_enumerate','enumerate.default'),
'core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.step_by':('range_step_by','step_by.default'),
'core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.collect':('iter_collect','collect.default (IteratorSliceIter T) out'),
'core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.rev':('iter_rev','rev.default'),
'core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.enumerate':('iter_enumerate','enumerate.default'),
'core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.step_by':('iter_step_by','step_by.default')}
semantics={
'collect':'Delegate to the supplied FromIterator on the same owned iterator; its errors and effects remain those of that dictionary.',
'rev':'Store the same iterator; subsequent iteration uses its back end. Constructor performs no element access or callback.',
'enumerate':'Store the same iterator and initial usize count zero; later checked count overflow may panic. Constructor invokes no callback.',
'step_by':'Zero step panics; otherwise store the same iterator and positive step. The documentation permits alternate timing of skipped-item pulls.'}
results=[]
for r in rows:
 n=r['name'];k=r['kernel_name'];leaf=n.rsplit('.',1)[-1]
 std=n.startswith(('core.','alloc.','Slice.','MutAArray.'))
 d=dict(r,category='std/core external or its carrier/helper' if std else 'MISCLASSIFIED project helper/adapter',verdict='UNDETERMINED',raw_static_occurrences=tokens[n],inherited_kernel_consumers=len(consumers[k]),consumer_examples=sorted(consumers[k])[:6],native='N/A: no Rust std counterpart',doc=None,proof=None)
 if n in p7:
  thm,const=p7[n];d.update(verdict='FAITHFUL',doc=iterator+leaf,proof='KSC2.'+thm,semantics=semantics[leaf],evidence='KSC2_L002: definitional equality to Aeneas.Std.core.iter.traits.iterator.Iterator.'+const+'; exact P7 objects pinned per receipt; KSC2_isolation.json checks the kit copy.',native='R002: iterator_defaults_and_range / shared_slice_and_windows_chunks; R003: collection Err/panic branches',obstruction_or_correction='Operation-local P7 transport; supplied iterator/collector interpretation is retained. No certification of a whole prepared claim or later adapter operations.')
 elif n=='core.option.Option.ok_or':
  d.update(verdict='FAITHFUL',doc=base+'option/enum.Option.html#method.ok_or',proof='KSC2.option_ok_or',semantics='Some maps to Rust Ok; None maps to Rust Err. The error is already evaluated before this value operation; it adds no library panic or borrow mutation.',evidence='KSC2_L003: universal case split for both arms, no axioms.',native='R002: option_result_branches, Some and None',obstruction_or_correction='Pure value-operation scope of TrustedStd; no claim about caller evaluation, arbitrary user Drop implementations, or unrelated borrowed-object invariants.')
 elif n=='core.iter.traits.iterator.Iterator.map.default':
  d.update(verdict='FAITHFUL',doc=iterator+'map',proof='KSC2.map_lazy',semantics='Create Map with the same iterator and closure state. Creation is lazy: no callback, panic or item mutation occurs here.',evidence='KSC2_L003: universal constructor equality.',native='R002: lazy callback count remains zero; R003: later collect callback panic control',obstruction_or_correction='Constructor only; map next/collect callback and borrow interpretations are separate.')
 elif n=='core.slice.Slice.windows':
  d.update(verdict='FAITHFUL',doc=base+'primitive.slice.html#method.windows',proof='KSC2.windows_zero; KSC2.windows_positive',semantics='Zero width panics. Positive width stores the original immutable slice and starts at index zero, including oversize widths (which yield no windows).',evidence='KSC2_L003: both constructor branches for all slices/widths.',native='R002: width 0,1,2,5 on empty/singleton/four-element slices',obstruction_or_correction='Forward Windows representation, with width>0 enforced by constructor; original immutable data is retained, no mutable write-back required.')
 elif n=='core.slice.iter.Windows.windowAt':
  d.update(verdict='FAITHFUL',doc=base+'primitive.slice.html#method.windows',proof='KSC2.window_contents',semantics='The helper denotes the contiguous immutable sublist drop(index).take(width). Library callers guard that a complete positive-width window exists.',evidence='KSC2_L003: generic exact list contents; this is a representation helper, not an independent public Rust function.',native='R002: overlapping windows and exact lengths',obstruction_or_correction='Faithful only as the guarded window representation helper used by the next law; no public out-of-range Windows API is invented.')
 elif n=='core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next':
  d.update(verdict='FAITHFUL',doc=base+'primitive.slice.html#method.windows',proof='KSC2.windows_next_some; KSC2.windows_next_none; KSC2.window_contents',semantics='If index+positive width fits, yield exactly that contiguous window and advance index by one. Otherwise yield None and remain exhausted; immutable backing data is unchanged.',evidence='KSC2_L003: universal fit/non-fit branches on constructor-reached positive-width states.',native='R002: empty, singleton, overlap, oversize, exhaustion',obstruction_or_correction='Forward-only observation relation. Constructor validity is established above; no fabricated width-zero input is passed off as a Rust-reachable state.')
 elif n=='core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT.next_back':
  d.update(verdict='FAITHFUL',doc=base+'iter/trait.DoubleEndedIterator.html#tymethod.next_back',proof='KSC2.shared_back_some; KSC2.shared_back_none',semantics='Return last remaining element and reduce back length while keeping the forward cursor. If forward cursor meets or exceeds remaining length, return None; no mutable write-back is needed.',evidence='KSC2_L003: both branches for arbitrary immutable slice/cursor, with list dropLast bound.',native='R002: empty/singleton/multiple, repeated back, mixed front/back and crossed cursors',obstruction_or_correction='Representation relation uses remaining interval [i,length); these are immutable items. It does not establish the separate mutable implementation.')
 elif 'IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.' in n and leaf in ['enumerate','rev','step_by']:
  stem={'enumerate':'mutable_enumerate','rev':'mutable_rev','step_by':'mutable_step'}[leaf]
  d.update(verdict='FAITHFUL',doc=iterator+leaf,proof='KSC2.'+stem+('_zero; KSC2.mutable_step_positive' if leaf=='step_by' else '_forward; KSC2.'+stem+'_restore'),semantics=semantics[leaf]+' The backward projection returns the supplied updated adapter.iter, rather than the original iterator.',evidence='KSC2_L019: P7 forward constructor and explicit backward projection; step zero panics and positive branch retains its continuation.',native='R002: mutable enumerate/rev/step_by updates; zero step panic',obstruction_or_correction='CONSTRUCTOR ONLY. A later use of mutable next_back, any/all/fold or collect does not receive fidelity credit from this row. In particular rev execution can depend on the refuted next_back.')
 elif n=='core.slice.iter.IterMut.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorMutT.next_back':
  d.update(verdict='UNFAITHFUL',doc=base+'iter/trait.DoubleEndedIterator.html#tymethod.next_back',proof='KSC2.mutable_back_repeats_consumed; KSC2.mutable_back_disagrees_with_empty_spec; KSC2.front_reaches_exhausted',semantics='Front and back share the same remaining interval. Once next has consumed the sole item, next_back must return None.',evidence='KSC2_L005/L023: [7], front cursor1 is reached by P7 next; kit returns Some7 after resetting shared cursor to0.',native='R002: same [7], next then next_back returns None',obstruction_or_correction='Pass s.i to shared next_back, or first reject s.i>=length. guardedBack proposes the latter (KSC2_BackCorrection), with generic exhaustion and active-tail write-back checks. A full continuation composition proof is still required; no corrected kit was installed.')
 elif 'IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.' in n and leaf in ['any','all','fold']:
  thm={'any':'mutable_any_loses_writeback','all':'mutable_all_loses_writeback','fold':'mutable_fold_loses_writeback'}[leaf]
  exp={'any':'[1,2], predicate adds10 to first mutable item then returns true: kit (true,[1,2]), Rust (true,[11,2]).','all':'[1,2], predicate adds10 to first mutable item then returns false: kit (false,[1,2]), Rust (false,[11,2]).','fold':'[1,2], callback adds10 to each mutable item then accumulates it: kit (23,[1,2]), Rust (23,[11,12]).'}[leaf]
  d.update(verdict='UNFAITHFUL',doc=iterator+leaf,proof='KSC2.'+thm,semantics='Iterator Item=&mut T permits callback mutation, retained after short-circuit, complete traversal, and panic before unwinding releases the borrow.',evidence=('KSC2_L018' if leaf=='fold' else 'KSC2_L005')+': exact kit observation under the value-only callback erasure. '+exp,native='R002: mutable_borrow_writeback_counterexamples; R003: empty/exhaustive/panic prefix writes; R004: 121 small-domain list fixtures',obstruction_or_correction='UNRESTRICTED mutable-callback model is refuted. FnMut F T Bool / FnMut F (B×T) B lacks updated T, and the next continuation is discarded. Model mutable arguments with an explicit updated item, thread closure F, invoke the saved next continuation on every returned item, and compose restoration. A read-only callback restriction would be a separate scoped law, not an unannounced repair. No claim these exact writes occur in deployed Rust.')
 elif std:
  method=leaf if leaf in ['any','all','fold','collect'] else 'next'
  d.update(doc=(base+'result/enum.Result.html#method.unwrap_or_else' if leaf=='unwrap_or_else' else iterator+method),semantics='Documented Rust iteration/value and callback behavior; panics/errors/borrow effects must be preserved, not inferred from small examples.',native='R002/R003 branch controls only; no complete universal association')
  if leaf=='unwrap_or_else':
   d.update(proof='KSC2.unwrap_or_else (value/control law only)',evidence='KSC2_L003 proves exactly one FnOnce call on Err, none on Ok, preserving the whole callback Result including fail/div. R002 tests skip/call/panic.',obstruction_or_correction='P7 supplies no constant of this name (L001). FnOnce capture ownership, mutable-capture restoration and destruction have no proved real-Rust interpretation here; the value/control equation plus fixtures is insufficient for unrestricted fidelity.')
  elif n=='core.slice.iter.Windows':
   d.update(doc=base+'primitive.slice.html#method.windows',evidence='KSC2_Simple establishes the forward constructor/next content laws; inherited KSA windows carrier roundtrip is reused as historical context only.',obstruction_or_correction='A custom representation type, not a std function. No complete representation relation for all Windows trait observations is proved; zero-width inhabitants exist although constructor forbids them. Only the specifically checked forward operations get credit.')
  elif 'IterMut' in n and leaf=='collect':
   d.update(evidence='The kit supplies value-only XRn_Join_iterator and returns original s after FromIterator; R002 collects real &mut references and mutates them after collection.',obstruction_or_correction='No alias relation between returned B (e.g. Vec<&mut T>) and original backing allocation, nor B-to-s write-back channel/continuation theorem. Native [1,2] becomes [11,12] through collected references. Exact full typed model/refinement is absent, so this row remains UNDETERMINED rather than treating value-copy collection as certified.')
  else:
   d.update(evidence='Inspected loop/delegation retains successive callback F while running; callbacks/remaining iterators are exercised by R002/R003.',obstruction_or_correction='No equality to a supplied P7 combinator for '+n+'. Need a full finite/infinite loop interpretation with callback-captured mutable-state restoration and failure-prefix effects. These wrappers eventually discard final F; no reached-callback purity/write-back theorem is supplied. Native branch fixtures do not close that universal obligation.')
 else:
  f=Path(r['file']).stem
  if f=='XRo_Join_Carriers':
   if n in ['inner','mapR']:
    why='Local mapping helper across Aeneas Result / Rust Result carriers, not an identified std external; requires its caller/source association and effect interpretation. Existing roundtrip/map lemmas are kit-relative.'
   else:why='Project carrier conversion '+k+' between the release-shaped kit and cohort records, not Rust std/core. Existing fieldwise roundtrips do not prove a raw-emission/source association or adopted installation.'
  elif f in ['XRo_Join_QmSampler','XRo_Join_OrdinaryDigits']:
   why='Alias of a project sampler arithmetic body/loop in the kit or a cohort, not a std external. Requires raw-emitted same-body association with the exact aliased owner; prior kit-relative equalities give no blanket emission credit.'
  elif f=='XRo_Join_PreparedBoundaries':why='Project prepared-model callback/dictionary '+k+'; requires exact adopted dictionary installation and raw-emission association, including source effects. It has no Rust std documentation counterpart.'
  elif f=='XRo_Join_Nonvacuity':why='Deliberately failing digest test dictionary, not production Rust std. Rejection/non-vacuity diagnostics cannot certify a deployed library operation.'
  elif f=='XSd_InverseShape':why='Diagnostic Nat spine recurrence used to expose the refuted inverse stand-in; not any Rust std/core item or a proposed faithful power model.'
  elif f=='XRn_Join_Field':why='Alias of project field representation (M31/CM31/QM31), not std; library semantics alone cannot associate this carrier with the shipped field type.'
  elif f=='XRn_Join_FieldExternal':why='Project field constant/conversion/comparison '+k+', not a Rust std external. Need its project-source/derived-operation association; no std model fidelity is inferred from carrier syntax.'
  elif n in ['le32','validChunk']:why='Project byte/canonicality helper '+k+' composing word decoding and field bounds. It is not a std item; must be checked against the exact project body and length/canonicality conditions.'
  else:why='Project helper '+k+', not an identified Rust std/core external; exact source association is outside std-library fidelity.'
  d.update(semantics='No independent Rust std/core item to specify.',evidence='Source definition inspected at '+r['file']+':'+str(r['line'])+'. Classification inherited from a lexical fallback, not a validated std mapping.',obstruction_or_correction=why)
 results.append(d)
results.sort(key=lambda d:(-d['inherited_kernel_consumers'],-d['raw_static_occurrences'],d['name'],d['file'],d['line']))
out=dict(inventory_sha256=assignment['inventory_sha256'],partition=assignment['sort'],results=results,counts=dict(collections.Counter(d['verdict'] for d in results)),adopted_path_dynamic_usage='UNDETERMINED: kit associations are explicitly not adopted-emission attribution; static counts are not execution frequency')
(E/'KSC2_verdicts.json').write_text(json.dumps(out,indent=2)+'\n')
lines=['## Per-model table','', 'Rows are ordered by inherited exact kernel-consumer count, then static raw-emission name occurrences, most used first. Counts are prioritization evidence only: the kit is not the adopted root, and the requested dynamic reached-path order is UNDETERMINED until the association/reachability gap closes. The source/emission literal call count is not a runtime frequency. The inherited kernel environments cover only their documented 618 explicit theorem names; no unqueried import candidate is upgraded. Full consumer examples and exact source hashes are in `KSC2_verdicts.json`.','', '| Declaration (original file:line) | Kernel/static uses | Verdict | Fidelity evidence and exact remaining scope |','|---|---:|---|---|']
for d in results:
 ref=f"`{d['kernel_name']}` ({Path(d['file']).name}:{d['line']})"
 evidence='Semantics: '+d['semantics']+' '+d['evidence']+' '+d['obstruction_or_correction']
 if d['proof']:evidence+=' Proof: `'+d['proof']+'`.'
 if d['doc']:evidence+=' [Rust 1.94.1]('+d['doc']+').'
 evidence+=' Native: '+d['native']+'.'
 lines.append(f"| {ref} | {d['inherited_kernel_consumers']}/{d['raw_static_occurrences']} | **{d['verdict']}** | {evidence} |")
(E/'KSC2_table.md').write_text('\n'.join(lines)+'\n')
print(out['counts'],'genuine std/helper rows',sum(d['category'].startswith('std') for d in results),'total',len(results))
