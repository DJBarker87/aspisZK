"""Statement-by-statement structural source binding under own-1.
This is source/reference evidence, not machine-code correspondence or a new extraction.
"""
from pathlib import Path
import subprocess,re,json,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdb2f-20261029';old=R/'evidence/pv-rdb2e-20261029';P=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
def tokens(s):
 return [m.group() for m in re.finditer(r'"(?:\\.|[^"\\])*"|//[^\n]*|/\*.*?\*/|[A-Za-z_][A-Za-z0-9_]*|0x[0-9A-Fa-f_]+|[0-9]+(?:[ui][0-9]+)?|::|->|=>|\S',s,re.S)if not m.group().startswith(('//','/*'))]
def body(s,name):
 t=tokens(s);i=next(i for i in range(len(t)-1)if t[i:i+2]==['fn',name]);a=t.index('{',i);b=a+1;d=1
 while d:
  d+=(t[b]=='{')-(t[b]=='}');b+=1
 return t[a:b]
def sha(s):return hashlib.sha256(s).hexdigest()
paths=['crates/aspis-r1-cost-probe/src/sampler.rs','crates/aspis-r1-cost-probe/src/transcript.rs','crates/aspis-r1-cost-probe/src/verifier.rs'];sources=[];rust={}
for p in paths:
 raw=subprocess.check_output(['git','show','HEAD:'+p]);rust[p]=raw.decode();sources.append(dict(path=p,blob=subprocess.check_output(['git','rev-parse','HEAD:'+p],text=True).strip(),sha256=sha(raw)))
for r in json.loads((old/'source-paths.json').read_text()):
 p=old/r['snapshot'];assert sha(p.read_bytes())==r['sha256'];sources.append(dict(path=str(p.relative_to(R)),deployed_path=r['path'],sha256=r['sha256']))
rows=[]
def bind(file,fn,steps):
 s=rust[file] if file in rust else (old/'source'/file).read_text();native=body(s,fn);joined=tokens('{'+''.join(x[0]for x in steps)+'}')
 assert native==joined,(file,fn,'unaccounted or changed source statement')
 rows.append(dict(source=file,function=fn,tokens_sha256=sha('\0'.join(native).encode()),complete_body_accounted=True,steps=[dict(source=src,model=mdl,law=law)for src,mdl,law in steps]))
sampler=paths[0]
bind(sampler,'low_base_p_digits',[
 ('let mut quotient: [u32; 8] = core::array::from_fn(|i| u32::from_le_bytes(block[4 * i..4 * i + 4].try_into().unwrap()));','initial Guard output=quotient; initialized=0..7; same immutable block','InitialFromFn.slice_bounds; InitialFromFn.slice_length; FromFnGuard.initialized_prefix'),
 ('let digits = core::array::from_fn(|_| {','Guard::initialized=d; FnMut captures the SAME quotient allocation','CapturedQuotient.body_association; CapturedQuotient.entire_capture'),
 ('let mut remainder = 0u64;','division initial remainder=0','Iterator.division_complete'),
 ('for limb in quotient.iter_mut().rev() {','IterMut(base,base+32); Rev.next delegates next_back; decrement end before return','RawCursor.back_bounds; RawCursor.backward_pointer; RawCursor.exact_empty'),
 ('let dividend = (remainder << 32) | u64::from(*limb);','read current allocation at returned address, high shift and low word','Iterator.division_body; RawHandles.Represents'),
 ('*limb = (dividend / u64::from(P)) as u32;','restore current quotient, never original captured snapshot','RawHandles.current_array_store; ArrayHandles.restore_total'),
 ('remainder = dividend % u64::from(P);','thread next remainder after write; drop scalar reference has no destructor','Iterator.division_body'),
 ('} remainder as u32 });','FnMut returns digit AND mutated quotient; Guard writes output[d], increments d; forget guard at8','CapturedQuotient.entire_capture; FromFnGuard.complete_capture'),
 ('debug_assert!(quotient[1..].iter().all(|&limb| limb == 0)); debug_assert!(quotient[0] <= 256);','removed by deployed release debug_assertions=false; no observation or panic here','inherited deployed profile/body binding; not active code'),
 ('(digits, quotient[0])','read FINAL quotient after all eight closure calls','CapturedQuotient.final_capture_read; Iterator.final_read_uses_returned_quotient')])
bind(sampler,'add_small_base_p',[
 ('for digit in digits {','array reference IntoIterator -> IterMut over same eight current words','RawCursor.forward_bounds; RawCursor.forward_pointer'),
 ('let sum = u64::from(*digit) + u64::from(addend);','read live digit; u32+u32 fits u64; current addend','Iterator.carry_body'),
 ('*digit = (sum % u64::from(P)) as u32;','store through returned address in current array; other words framed','RawHandles.current_array_store; ArrayHandles.frame'),
 ('addend = (sum / u64::from(P)) as u32; }','thread addend and advanced cursor; drop &mut u32 is inert','Iterator.carry_body; Iterator.carry_loop'),
 ('debug_assert!(addend <= 1);','inactive in release','deployed debug_assertions=false'),
 ('addend != 0','return carry with restored full array','Iterator.carry_complete')])
bind(sampler,'ordinary_sample',[
 ('let (digits, _) = low_base_p_digits(block);','call with current immutable block; discard only final scalar quotient','Iterator.low_complete'),
 ('decode8(digits)','all eight initialized digits consumed in exact field order; no mutation continuation discarded','Iterator.ordinary_complete; SamplerCalls.ordinary_callback')])
bind(sampler,'gamma_sample',[
 ('let (mut digits, quotient) = low_base_p_digits(block);','receive initialized digits and final quotient','Iterator.low_complete; CapturedQuotient.final_capture_read'),
 ('let wrapped = add_small_base_p(&mut digits, quotient + 1);','first carry writes current digits before wrapped branch','Iterator.carry_complete; RawHandles.current_array_store'),
 ('if wrapped { let wrapped_again = add_small_base_p(&mut digits, 1); debug_assert!(!wrapped_again); }','optional second carry uses returned current digits; inactive debug assertion','Iterator.second_carry_current; Iterator.gamma_complete'),
 ('decode8(digits)','decode after BOTH restoration branches','SamplerCalls.gamma_callback')])
bind(paths[1],'scalar',[
 ('let block=self.block(row,payload);','same block call and transcript state effects retained, not proved here','retained block law; native source call prefix identical'),
 ('let out=if nonzero {crate::sampler::gamma_sample(&block)} else {crate::sampler::ordinary_sample(&block)};','actual verifier source uses ORIGINAL sampler; prover host_sampler not substituted','VerifierCalls.scalar_consumed_call'),
 ('crate::trace::value(4,row as usize,out); out','same trace tag4, same row cast, same output and world; no trace elimination','VerifierCalls.scalar_consumed_call')])
bind('sha256-soft.rs','compress',[
 ('let mut block_u32 = [0u32; BLOCK_LEN];','sixteen destination words; values irrelevant after complete overwrite','LoadWrites.no_stale_word'),
 ('let mut state_cpy = *state;','copy all eight initialized words from current native core state','NativeShaFrame.simultaneous_restore; SoftOuter.blocks'),
 ('for block in blocks {','same immutable block list, in order; local state_cpy threaded','SoftOuter.compression_trace'),
 ('for (o, chunk) in block_u32.iter_mut().zip(block.chunks_exact(4)) {','IterMut16 and chunks_exact64/4 both sixteen; current output handle','LoadWrites.zip_trip_count; LoadWrites.chunk_exact'),
 ('*o = u32::from_be_bytes(chunk.try_into().unwrap()); }','four bytes in source order; conversion cannot fail; each current word overwritten','LoadWrites.every_store; inherited ShaBytes lane0..15 exact operand bindings'),
 ('sha256_digest_block_u32(&mut state_cpy, &block_u32); }','exact bound software word-block extraction, complete returned state','FallbackBlockTotal.total; SoftOuter.compression_trace'),
 ('*state = state_cpy;','whole final state copy, including empty-list case; all other native fields framed','SoftOuter.final_store; NativeShaFrame.simultaneous_restore')])
bind('core-array-mod.rs','from_fn',[
 ('try_from_fn(NeverShortCircuit::wrap_mut_1(f)).0','same FnMut wrapper; never short-circuits a successful scalar result','FromFnGuard.complete_capture; CapturedQuotient.entire_capture')])
bind('core-array-mod.rs','try_from_fn_erased',[
 ('let mut guard = Guard { array_mut: buffer, initialized: 0 };','exclusive initialized-prefix guard starts at zero, same output allocation','FromFnGuard.guarded; CapturedQuotient.guardBody'),
 ('while guard.initialized < guard.array_mut.len() {','guard count is index; element count8; actual live buffer','CapturedQuotient.body_association; InitialFromFn.slice_bounds'),
 ('let item = generator(guard.initialized).branch()?;','same captured state is supplied to every FnMut invocation; scalar NeverShortCircuit branch cannot Break','CapturedQuotient.invoke; FromFnGuard.initialized_prefix'),
 ('unsafe { guard.push_unchecked(item) }; }','write initialized slot before increment; no stale output overwritten later','FromFnGuard.store_before_increment; CapturedQuotient.body_association'),
 ('mem::forget(guard); ControlFlow::Continue(())','fully initialized; disarm drop guard and return; scalar fields have no user Drop','FromFnGuard.complete_capture')])
bind('core-array-mod.rs','push_unchecked',[
 ('unsafe { self.array_mut.get_unchecked_mut(self.initialized).write(item);','current output slot is exactly initialized; native raw store, no captured snapshot','RawHandles.current_array_store (u32); FromFnGuard.initialized_prefix'),
 ('self.initialized = self.initialized.unchecked_add(1); }','increment only after store; bound0..7 makes unchecked_add valid','FromFnGuard.store_before_increment; CapturedQuotient.body_association')])
bind('core-array-mod.rs','drop',[
 ('debug_assert!(self.initialized <= self.array_mut.len());','inactive in deployed release; initialized bound maintained','FromFnGuard.store_before_increment'),
 ('unsafe { self.array_mut.get_unchecked_mut(..self.initialized).assume_init_drop(); }','on unwind only initialized u32 prefix is dropped; u32 has no destructor, captured quotient not rolled back','source scalar drop glue; V370 compiler preservation retained')])
bind('core-iter-rev.rs','next',[
 ('self.iter.next_back()','delegate to the same inner iterator, no copy/reset/duplicate','RawCursor.back_bounds; Iterator.back_source')])
# Both algorithms use exactly the same sixteen macro stages and rotation order.
soft=(old/'source/sha256-soft.rs').read_text();hard=(old/'source/sha256-x86.rs').read_text()
pattern=r'^\s*((?:schedule_)?rounds4!\([^;]+\);)'
a=[v for v in re.findall(pattern,soft,re.M)if "$"not in v];b=[v for v in re.findall(pattern,hard,re.M)if "$"not in v];assert [tokens(v)for v in a]==[tokens(v)for v in b]and len(a)==16
hardware=dict(source='sha256-x86.rs',conditional='SHA_NI_IntrinsicsSemantics',macro_stages=16,source_sha256=sha(hard.encode()),proof='ShaNi.word_block_semantics; ShaNi.digest_blocks_refinement; ShaNi.conditional_dispatch',instruction_groups=['add32','rnds2','shuffle0x0E followed by rnds2 (upper unused lanes differ)','msg1','alignr4','msg2','state loadu/shuffleB1/shuffle1B/alignr8/blendF0 pack','four loadu/byte-shuffle MASK inputs','final shuffle1B/shuffleB1/blendF0/alignr8/two storeu unpack'],pending='owner item3',added_to_T=False)
# Actual finalizer copy, pad branches and type aliases were token-bound in the inherited source gate.
prior=json.loads((old/'structural-binding.json').read_text());assert all(r.get('byte_equal',True)for r in prior['checks'])
result=dict(evidence_class='structural (K-1 substitute), source level under own-1',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),sources=sources,bindings=rows,hardware=hardware,sha_native_association=dict(types='Sha256VarCore(state8,count64); BlockBuffer<U64,Eager>(GenericArray bytes64,pos); Output GenericArray bytes32',source_fields='all source fields projected as owned initialized sequences; compiler representation/layout preservation retained V370',law='NativeShaFrame.all_native_fields; NativeShaFrame.simultaneous_restore; NativeShaFrame.software_all_fields',padding='inherited exact digest_pad/len64_padding_be model, position0..63, suffix8, both callbacks and pos reset',serialization='all eight state words, chunks_exact_mut(4), exact to_be_bytes copy, inherited ShaSerialize law'),library_association=dict(IterMut='non-ZST ptr/end; next postincrements old ptr; next_back empty guard then predecrement end; current exclusive array address mapped by RawHandles',Rev='next -> inner.next_back exactly',FnMut='capture allocation persists; invoke returns digit,current quotient; Guard writes item then increments initialized; forget at8',drop_glue='all elements u8/u32, reference and iterator values have no user Drop; initialized-prefix guard cleanup on unwind drops only scalar words; release-active failure branches accounted by source bounds/P nonzero',compiler='V370 and D381/D386 explicitly retained; no machine-code equivalence claimed'),inherited_evidence=['../pv-rdb2e-20261029/structural-binding.json','../pv-rdb2e-20261029/fallback-source-binding.json','../pv-rdb2e-20261029/sha-stage-binding.json'],T=['entropy_law','entropy_kernel','observation'],composition_trust='reclassification within existing tool trust, never premise removal')
(E/'own1-binding.json').write_text(json.dumps(result,indent=2)+'\n');print('PASS source statement coverage:',len(rows),'whole source bodies;16 matched hardware macro stages. Lean laws must separately pass.')
