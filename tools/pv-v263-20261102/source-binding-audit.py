"""Fail-closed source/control audit; never reclassify an incomplete model as bound."""
from pathlib import Path
import hashlib,json,subprocess,re
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-v263-20261102'
L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
sha=lambda b:hashlib.sha256(b).hexdigest()
pins=json.loads((E/'frozen-source.json').read_text());sources={}
for pin in pins['files']:
 p=E/'inputs'/pin['path'];b=p.read_bytes()
 assert sha(b)==pin['sha256'],p
 frozen=subprocess.check_output(['git','show',pin['revision']+':'+pin['path']])
 assert b==frozen,p
 sources[pin['path']]=dict(path=str(p.relative_to(R)),sha256=sha(b),frozen_revision=pin['revision'],git_blob=pin['blob'])
host=(E/'inputs/crates/aspis-r1-cost-probe/src/host_work.rs').read_text()
pool=(E/'inputs/docs/research/v8-r0-zk-20261009/c3/check/src/native_workers.rs').read_text()
models={n:(L/('PV_V263_'+n+'.lean')).read_text() for n in ['MapSpine','SourceSpine','SourceItems','WorkerControl','DeferredJoin','GrantRun','VectorLoop']}
rows=[]
def row(name,src,snippet,model,needle,remaining):
 assert snippet in src,(name,'source')
 assert needle in models[model],(name,'model')
 rows.append(dict(step=name,source_fragment=snippet,source_fragment_sha256=sha(snippet.encode()),model='R1Z.PV_V263_'+model,model_fragment=needle,status='control correspondence checked; primitive adequacy retained',remaining=remaining))
row('force=true and outer count16',host,'pool::ordered_families(pool::THREADS,|k|','SourceSpine','(List.range 16)', ['pool exact collect specialization'])
row('inner range',host,'let (a,b)=pool::range(n,k);','SourceItems','PV_V263_Family.indices n k',['Range.usize_safe is accepted; compiler V370 retained'])
row('item capacity',host,'let mut out=Vec::with_capacity(b-a);','SourceItems','.capacity 0 k (PV_RunJoin_WorkRange35.width n k)',['Vec capacity and heap representation; V400-257-layout/lowering'])
row('callback before store',host,'out.push(f(i));completed+=1;','SourceItems','PV_V263_World.bind (callback i) fun value =>',['logical list value is retained; native heap stores not yet related'])
row('item push',host,'out.push(f(i));completed+=1;','SourceItems','.push 0 k (i-PV_RunJoin_WorkRange35.start n k) layouts.item',['store of value and increment completed; actual Vec carrier'])
row('returned completed',host,'(out,completed)','SourceSpine','pure [(values,values.length)]',['logical completed=successful loop iterations; no explicit bounded machine increment proof'])
row('host output capacity',host,'let mut out=Vec::with_capacity(n);','SourceSpine','.capacity 5 0 n layouts.item',['actual layout/capacity, allocation and heap relation'])
row('host source-order append',host,'out.append(&mut chunk);','SourceSpine','.append 5 0 length chunk.length layouts.item',['drained source vector, heap move, actual Vec representation'])
row('host chunk drop',host,'for (k,(mut chunk,completed)) in chunks.into_iter().enumerate() {','SourceSpine','.drop 0 k layouts.item',['implicit IntoIter/enumerate and closure drops not explicitly represented'])
row('nested TLS branch',pool,'if (n < THREADS*2 && !force) || is_worker()','SourceSpine','let active ← runtime.os.answer (.tlsRead 0)',['force=true makes first disjunct false; TLS native lifetime/codec'])
row('outer Active lifetime',pool,'let _active = Active::enter();','SourceSpine','withActive runtime.os .abort 0',['TLS failure/diagnostic/event adequacy'])
row('worker Active outside catch',pool,'std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {','SourceSpine','withActive runtime.os .abort k (catchPanic .abort',['panic=abort selected; native hooks/diagnostics are not Bytes []'])
row('one-family collect',pool,'(a..b).map(&f).collect::<Vec<T>>()','SourceSpine','.collect 1 k 1 layouts.family',['specialized std collect must establish capacity/store/drop ordering'])
row('handles empty',pool,'let mut handles = Vec::new();','SourceSpine','.empty 2 0 layouts.handle',['capacity metadata and growth lowering'])
row('spawn loop',pool,'for k in 1..THREADS','SourceSpine',"(List.range' 1 15)",['thread packet/stack/TLS allocation; V400-257-lowering'])
row('spawn then handles push',pool,'handles.push(scope.spawn(move || run(k)))','SourceSpine','.push 2 0 (k-1) layouts.handle',['std spawn and handle growth; no worker-result oracle'])
row('caller run before join',pool,'let first = run(0);','SourceSpine','let first ← caughtFamily runtime layouts n 0 callback',['join-late is a candidate scheduling witness; native realisation remains'])
row('caught capacity',pool,'let mut chunks = Vec::with_capacity(THREADS);','SourceSpine','.capacity 3 0 16 layouts.caught',['actual Result/Join payload layouts'])
row('first caught push',pool,'chunks.push(first);','SourceSpine','.push 3 0 0 layouts.caught',['heap store and capacity relation'])
row('join retains errors',pool,'match handle.join() {Ok(v)=>v,Err(p)=>Err(p)}','DeferredJoin','match joinError with | none => caught | some p => .error p',['std join/panic payload adequacy; callback action not answered by OS'])
row('remaining caught pushes',pool,'chunks.push(match handle.join()','SourceSpine','.push 3 0 length layouts.caught',['heap store and IntoIter/handle ownership drops'])
row('scope return before pool allocation',pool,'let mut out = Vec::with_capacity(n);','SourceSpine','runtime.os.answer (.cleanup 0)',['scope packets, guards, handle IntoIter and closure lifetimes'])
row('pool output capacity16',pool,'let mut out = Vec::with_capacity(n);','SourceSpine','.capacity 4 0 16 layouts.family',['pool n=16; exact capacity layout'])
row('source-order error after joins',pool,'Err(p)=>std::panic::resume_unwind(p)','SourceSpine','| _,.error p::_ => fun w => ⟨.fault (.abort p),w,[]⟩',['panic diagnostics/native formatting not yet associated'])
row('pool append and emptied family drop',pool,'Ok(mut v)=>out.append(&mut v)','SourceSpine','.drop 1 length layouts.family',['actual drained Vec heap relation and IntoIter drop order'])
row('TLS replace',pool,'ACTIVE.with(|a| a.replace(true))','WorkerControl','runtime.answer (.tlsReplace thread true)',['std LocalKey/Cell and thread lifetime lowering'])
row('TLS restore',pool,'ACTIVE.with(|a| a.set(self.0))','WorkerControl','runtime.answer (.tlsRestore thread previous)',['std LocalKey/Cell and thread lifetime lowering'])
row('exact inner Vec value store',host,'out.push(f(i));completed+=1;','VectorLoop','lift (alloc.vec.Vec.push out a)',['Aeneas Vec carrier/store value; physical capacity/heap relation retained'])
row('explicit completed increment',host,'out.push(f(i));completed+=1;','VectorLoop','ids next (completed+1)',['granting_loop proves completed exactly; machine arithmetic/source lowering retained'])
old=models['MapSpine'];old_items=old[old.index('def items '):old.index('def family ')]
assert '.push 0' not in old_items
new=models['SourceSpine'];assert 'abbrev items := @PV_V263_SourceItems.run' in new
unbound=[
 'Outer pool/host alloc.vec.Vec carrier and all physical heap representations; draining appends/capacity metadata. VectorLoop supplies the inner Vec carrier only',
 'Pinned std collect specialization and all implicit IntoIter/closure/handle/scope/drop glue',
 'Native realisation of join-late schedule and EVH event codec',
 'Exact deployed callback captures and bounded callback success, including op227 bridge and other source laws',
 'Actual opsNative installation plus stateful NativeControl capture; no total source projection on faults',
 'V400-257-entry/layout/lowering/callback/answer-timing, V370 compiler cohort; V183 remains suspended K-3']
revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
out=dict(source_revision=revision,frozen_source_revision=pins['freeze'],evidence_class='mechanically checked source/control correspondence inventory; NOT a complete own-1 binding',features=['r1p-check','aspis-r1-cost-probe/ct-host-prover'],public_work_trace=False,profile={'rustc':'1.94.1','profile':'release','panic':'abort','overflow_checks':False,'debug_assertions':False},sources=sources,models={n:sha(s.encode()) for n,s in models.items()},steps=rows,candidate_omission={'old':'MapSpine.items has no item-push method step','replacement':'SourceItems.step and revised SourceSpine.items','logical_values':'Revised SourceSpine is List; separate VectorLoop uses actual inner Vec and explicit pushes. No outer Vec or native heap proof'},unbound=unbound,complete_source_binding=False,op257_installed=False,actual_reached_callback_law_discharged=False,nonempty_P=False)
(E/'source-binding-audit.json').write_text(json.dumps(out,indent=2)+'\n')
print('Frozen sources match; '+str(len(rows))+' source/control rows checked; complete binding INCOMPLETE; op257 NOT installed')
