"""Pin source spans and explicit partial source-to-model review; no closure claim.

This is a coverage preflight, not an AST equivalence proof. Nonempty entries
identify exactly which symbolic laws have to be checked in the final audit.
"""
from pathlib import Path
import json,hashlib,re,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-ownc-20261029'
rows=json.loads((R/'evidence/pv-ownb-20261029/deployed-collector-sources.json').read_text())
# Compare current deployed source bytes with the inherited captures, read only.
code='from pathlib import Path\nimport json,hashlib\nrows='+repr([{k:x[k] for k in ['path','sha256']} for x in rows])+"\nfor x in rows:x['actual']=hashlib.sha256(Path(x['path']).read_bytes()).hexdigest();x['ok']=x['actual']==x['sha256']\nprint(json.dumps(rows))\n"
p=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True,capture_output=True);assert p.returncode==0,p.stderr
pins=json.loads(p.stdout);assert all(x['ok'] for x in pins)
by={Path(x['path']).name:x for x in rows}
def span(file,anchor):
 s=by[file]['text'];a=s.index(anchor);brace=s.index('{',a);depth=1;i=brace+1
 # Anchors identify code bodies; braces in comments are not present in selected spans.
 while depth:
  if s[i]=='{':depth+=1
  if s[i]=='}':depth-=1
  i+=1
 text=s[a:i]
 return dict(file=file,start_line=s[:a].count('\n')+1,end_line=s[:i].count('\n')+1,sha256=hashlib.sha256(text.encode()).hexdigest(),text=text)
items=[]
def add(file,anchor,checks,laws,differences):
 b=span(file,anchor);s=b['text'];last=-1
 for check in checks:
  at=s.index(check,last+1);assert at>last;last=at
 b.update(ordered_source_statements=checks,model_laws=laws,differences=differences,status='partial symbolic binding; not a complete structural gate')
 items.append(b)
add('into_iter.rs','fn next(&mut self)', ['if T::IS_ZST','if self.ptr == non_null!(self.end, T)','let old = self.ptr','self.ptr = unsafe { old.add(1) }','Some(unsafe { ptr.read() })'],['PV_OWNC_SourceIterator.available','PV_OWNC_SourceIterator.exhausted','PV_OWNC_ReadPointer.advance_pointer'],['ZST branch unreachable for Link size8; symbolic indices use byte address base+8*read; active-byte representation inherited ownb, compiler layout retained'])
add('into_iter.rs','fn try_fold<B, F, R>', ['if T::IS_ZST','while self.ptr != non_null!(self.end, T)','let tmp = unsafe { self.ptr.read() }','self.ptr = unsafe { self.ptr.add(1) }','accum = f(accum, tmp)?','R::from_output(accum)'],['PV_OWNC_FoldSource.step_binding','PV_OWNC_SourceLoop.snapshot_binding','PV_OWNC_SourceLoop.completed'],['Generic ? branch is specialized to total path filter plus Result<_,!> sink; predicate-panic cleanup must be reviewed independently; no Result/world equality for the whole callback follows'])
add('into_iter.rs','pub(super) fn forget_allocation_drop_remaining', ['let remaining = self.as_raw_mut_slice()','self.cap = 0','self.buf = RawVec::new().non_null()','self.ptr = self.buf','self.end = self.buf.as_ptr()','ptr::drop_in_place(remaining)'],['PV_OWNC_HeaderStores.cap','PV_OWNC_HeaderStores.buf','PV_OWNC_HeaderStores.ptr','PV_OWNC_HeaderStores.endPtr','PV_OWNC_SourceDetached.reset_no_free'],['Dangling aligned Link pointer represented by2; pointer identity becomes unobservable once header has cap0 and no live slice; saved tail is Link POD; this does not permit omitting non-POD destruction'])
add('in_place_drop.rs','fn drop(&mut self)', ['ptr::drop_in_place(ptr::slice_from_raw_parts_mut(self.inner, self.len()))'],['PV_OWNC_GuardCleanup.prefix_empty'],['No runtime destructor event for Link POD; source drop invocation is retained as a logical control-flow stage'])
add('in_place_drop.rs','impl<Src, Dest> Drop', ['let _drop_allocation','RawVec::<Src>::from_nonnull_in','drop_in_place(core::ptr::slice_from_raw_parts_mut::<Dest>'],['PV_OWNC_GuardCleanup.original_layout','PV_OWNC_GuardTransfer.owned','PV_OWNC_GuardReturn.returned_valid'],['RawVec allocation guard deallocates original source layout after POD prefix; generic panicking element branches not instantiated for Link'])
add('in_place_collect.rs','fn from_iter_in_place<I, T>', ['let (src_buf, src_ptr, src_cap', 'SpecInPlaceCollect::collect_in_place', 'let src = unsafe', 'let dst_guard =', 'src.forget_allocation_drop_remaining()', 'if needs_realloc', 'mem::forget(dst_guard)', 'Vec::from_parts'], ['PV_OWNC_Specialization.no_shrink','PV_OWNC_SourceLoop.completed','PV_OWNC_InPlaceResult.guarded','PV_OWNC_CursorVector.initialized'], ['Source header/guard constructor instance is still needed; debug assertions are disabled in deployed release; equal Link layouts select no shrink, so shrink panic/null handler branch is unreachable for this specialization; no arbitrary-layout closure asserted'])
manifest=json.loads((E/'frozen-proof-manifest.json').read_text())
for item in items:
 assert all('R1Z.'+law in manifest['roots'] for law in item['model_laws'])
 item['local_model_laws_checked']=True
# Retain every rest-of-callback gap rather than treating token matching as proof.
gaps=[
 dict(stage='full source carrier',missing='bind typed source Link fields to the padding-aware representation; compiler-chosen layout evidence stays reclassification at retained V370 D381/D386, not a machine-code correspondence task'),
 dict(stage='filter loop and guards',missing='compose guard state, saved tail, unwind and byte filtering into one complete Result/world source instance'),
 dict(stage='translation',missing='bind every producer/consumer mutation and checked endpoint branch into full Link representation'),
 dict(stage='reserve and pushes',missing='instantiate realloc prefix/ownership transport and all 72 initialized pushes'),
 dict(stage='FlatMap collect',missing='TrustedLen destination array iterator initialization, source teardown and separate allocation association'),
 dict(stage='sort/dedup',missing='bind every in-place permutation/dedup move, initialized length and POD tail drop'),
 dict(stage='consumption',missing='compose full byte/world source instance with PV_RDB2D_CollectorProgram.complete and full value law')]
j=dict(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),ruling='own-1 D429',compiler_boundary='V370 D381/D386 retained',scope='partial source coverage preflight, not complete structural (K-1 substitute) gate',pins=pins,items=items,unclosed=gaps,whole_row_restored=False)
(E/'source-binding.json').write_text(json.dumps(j,indent=2)+'\n')
print('source pins',len(pins),'reviewed spans',len(items),'unclosed stages',len(gaps))
