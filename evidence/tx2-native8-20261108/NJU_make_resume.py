"""Value/log interpretation of retained emission; zero extraction runs."""
from pathlib import Path
import subprocess,re,hashlib,json
E=Path(__file__).resolve().parent
path='evidence/tx2-native2-20261107/NID_ResumeEmissionFuns.lean'
s=subprocess.check_output(['git','show','HEAD:'+path],text=True)
a=s.index('def verifier.resume\n');b=s.index('\n/--',a)
body=s[a:b]
body=body.replace('def verifier.resume\n','def run (reservation : NP6_StdModel.Reservation)\n')
body=body.replace('(aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)','(d : AspisR1Stage2.aspis_core.digest.Digest32 H)')
body=body.replace('aspis_coredigestDigest32Inst','(NIL_FreshOps.digest d)')
body=body.replace('Result (core.result.Result (verifier.Prepared × verifier.Accumulator)\n    verifier.Error)','NJU_Log.Run Event (core.result.Result (verifier.Prepared × verifier.Accumulator)\n    verifier.Error)')
subs={
 0:'CheckpointBytes4Ops.ne',1:'CheckpointBytes4Ops.eq',2:'NIL_FreshOps.mapError',
 3:'(fun inst it f=>NJU_Log.record (.headerAny it) (NIL_FreshOps.any inst it f))',4:'(fun x=>ok x)',5:'(fun x=>ok x)',
 6:'(ok (NIL_Carriers.unK ⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩))',
 7:'(fun copy n value=>NJU_Log.record (.filled n value) (NIL_FreshOps.filled (NJC_FilledClause.reserved reservation) copy n value))',
 11:'(fun bytes cursor=>NJU_Log.record (.semantic bytes cursor) (NIL_FreshOps.semantic bytes cursor))',
 12:'(fun bytes cursor weights=>NJU_Log.record (.weights bytes cursor weights) (NIL_FreshOps.weights bytes cursor weights))',
 13:'(fun queries=>NJU_Log.record (.validate queries) (NJC_ValidateEmission.verifier.validate_checkpoint_queries queries))',
 14:'(fun reader=>NJU_Log.record (.k reader) (NIL_FreshOps.readK reader))',
 15:'(fun reader=>NJU_Log.record (.e reader) (NIL_FreshOps.readE reader))',
 16:'(fun n reader=>NJU_Log.record (.raw n reader) (NJC_ConcreteUnwrap.raw n reader))',
 17:'(fun v=>CheckpointBytes4Ops.checkpointSize (NIL_Carriers.variant v))',
 18:'(fun v=>CheckpointBytes4Ops.finalLen (NIL_Carriers.variant v))',
 19:'(fun v=>CheckpointBytes4Ops.tag (NIL_Carriers.variant v))'}
body=re.sub(r'\bNID_call_(\d+)\b',lambda m:subs[int(m[1])],body)
for chunks in ['s3','s5','s9']:
 call='(NIL_FreshOps.digest d).digest hash '+chunks
 body=body.replace(call,'NJU_Log.record (.digest '+chunks+') ('+call+')')
# Name every logging operation to avoid repeated higher-order inference.
for number,name in [(3,'recordAny'),(7,'(recordFilled reservation)'),(11,'recordSemantic'),(12,'recordWeights'),(13,'recordValidate'),(14,'recordK'),(15,'recordE'),(16,'recordRaw')]:
 body=body.replace(subs[number],name)
for chunks in ['s3','s5','s9']:
 call='(NIL_FreshOps.digest d).digest hash '+chunks
 body=body.replace('NJU_Log.record (.digest '+chunks+') ('+call+')','recordDigest d hash '+chunks)
# Share the pure query array before the deep Try suffix. The unshared record
# hit default elaboration recursion depth at its second 22-cell constructor.
arrays=[m for m in re.finditer(r'\(Array.make\s+22#usize \[[^\]]+\]\)',body,re.S) if 'i8' in m[0]]
assert len(arrays)==2,len(arrays)
query_array=arrays[0][0]
body=re.sub(r'\(Array.make\s+22#usize \[[^\]]+\]\)',lambda m:'queryValues' if 'i8' in m[0] else m[0],body,flags=re.S)
marker='                              let r35 ←'
assert marker in body
body=body.replace(marker,'                              let queryValues := '+query_array+'\n'+marker)
def split_block(text,marker,indent,call):
 start=text.index(marker);lines=text[start:].splitlines(True);size=0
 for i,line in enumerate(lines):
  if i and line.strip() and len(line)-len(line.lstrip())<indent:break
  size+=len(line)
 segment=text[start:start+size]
 segment=''.join(line[indent:] if line.strip() else line for line in segment.splitlines(True))
 return text[:start]+' '*indent+call+'\n'+text[start+size:],segment
common='''(reservation : NP6_StdModel.Reservation) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (bytes : Slice U8)
 (v : transport.Variant) (i4 : U8) (end1 : Usize)'''
fields='''(state a3 a4 : Array U8 32#usize) (val val1 val2 val3 : E) (val4 : K)'''
args='reservation d bytes v i4 end1 state a3 a4 val val1 val2 val3 val4'
body,tail=split_block(body,'                                let r36 ←',32,
 'finishTailG '+args+' queryValues r34')
body,queries=split_block(body,'                              let (a5, r13) ←',30,
 'queryBlockG '+args+' r12')
# Split the 22 unrolled raw reads into tail continuations (8/8/6).
# No bind is reassociated: each helper is the literal last continuation.
queries,mid=split_block(queries,'let (a13, r21) ←',0,
 'queryMidG '+args+' '+' '.join('i'+str(i) for i in range(8,16))+' r20')
mid,endqueries=split_block(mid,'let (a21, r29) ←',0,
 'queryEndG '+args+' '+' '.join('i'+str(i) for i in range(8,24))+' r28')
body,raw=split_block(body,'                    let (state, r) ←',20,
 'resumeBodyG reservation d bytes v i4 end1')
result='(core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error)'
specs=[('finishTail',common+'\n '+fields+'\n (queryValues : Array U32 22#usize) (r34 : verifier.Reader)',tail),
 ('queryEnd',common+'\n '+fields+'\n ('+' '.join('i'+str(i) for i in range(8,24))+' : U32) (r28 : verifier.Reader)',endqueries),
 ('queryMid',common+'\n '+fields+'\n ('+' '.join('i'+str(i) for i in range(8,16))+' : U32) (r20 : verifier.Reader)',mid),
 ('queryBlock',common+'\n '+fields+'\n (r12 : verifier.Reader)',queries),
 ('resumeBody',common,raw)]
def remove_records(text):
 needle='NJU_Log.record'
 def end_paren(i):
  assert text[i]=='('
  level=0
  for j in range(i,len(text)):
   if text[j]=='(':level+=1
   elif text[j]==')':
    level-=1
    if level==0:return j+1
  raise ValueError('unbalanced record')
 while needle in text:
  start=text.index(needle);i=start+len(needle)
  while text[i].isspace():i+=1
  event_end=end_paren(i);i=event_end
  while text[i].isspace():i+=1
  call_end=end_paren(i)
  text=text[:start]+text[i:call_end]+text[call_end:]
 return text
helpers=''
for name,params,segment in specs:
 helpers+='def '+name+'G '+params+' : NJU_Log.Run Event '+result+' := do\n'
 helpers+=''.join(' '+line for line in segment.splitlines(True))+'\n'
 reference=remove_records(segment)
 for source_name,target in [('recordRaw','NJC_ConcreteUnwrap.raw'),('recordK','NIL_FreshOps.readK'),('recordE','NIL_FreshOps.readE'),('recordSemantic','NIL_FreshOps.semantic'),('recordWeights','NIL_FreshOps.weights'),('recordValidate','NJC_ValidateEmission.verifier.validate_checkpoint_queries'),('recordAny','NIL_FreshOps.any')]:reference=reference.replace(source_name,target)
 reference=reference.replace('(recordFilled reservation)','(NIL_FreshOps.filled (NJC_FilledClause.reserved reservation))')
 for old in ['finishTail','queryEnd','queryMid','queryBlock','resumeBody']:reference=reference.replace(old+'G',old+'R')
 helpers+='def '+name+'R '+params+' : Result '+result+' := do\n'
 helpers+=''.join(' '+line for line in reference.splitlines(True))+'\n'
reference=remove_records(body).replace('def run ','def runRef ')
reference=reference.replace('NJU_Log.Run Event','Result')
for source_name,target in [('recordRaw','NJC_ConcreteUnwrap.raw'),('recordK','NIL_FreshOps.readK'),('recordE','NIL_FreshOps.readE'),('recordSemantic','NIL_FreshOps.semantic'),('recordWeights','NIL_FreshOps.weights'),('recordValidate','NJC_ValidateEmission.verifier.validate_checkpoint_queries'),('recordAny','NIL_FreshOps.any')]:reference=reference.replace(source_name,target)
reference=reference.replace('recordDigest d hash','(NIL_FreshOps.digest d).digest hash')
for old in ['finishTail','queryEnd','queryMid','queryBlock','resumeBody']:reference=reference.replace(old+'G',old+'R')
body=helpers+body+'\n'+reference

header='''import NJU_Log
import NJR_ReservationSites
set_option autoImplicit false
noncomputable section
namespace NJU_ResumeObserved
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission
abbrev K := aspis_core.field.QM31
abbrev E := aspis_core.field.wide_exact.WideExact
abbrev R (A : Type) := Result (core.result.Result A verifier.Error)

/-- Full replies at actual entered resume sites. This is a source-log stage;
its native cut association must still be assembled and is not a root premise. -/
inductive Event where
 | digest (chunks : Slice (Slice U8)) (reply : Result (Array U8 32#usize))
 | headerAny (it : core.slice.iter.Iter U8) (reply : Result (Bool × core.slice.iter.Iter U8))
 | raw (n : Usize) (reader : verifier.Reader) (reply : Result (Array U8 n × verifier.Reader))
 | k (reader : verifier.Reader) (reply : Result (core.result.Result K verifier.Error × verifier.Reader))
 | e (reader : verifier.Reader) (reply : Result (core.result.Result E verifier.Error × verifier.Reader))
 | semantic (bytes : Slice U8) (cursor : Usize) (reply : R (Array K 10#usize × Usize))
 | weights (bytes : Slice U8) (cursor : Usize) (before : alloc.vec.Vec K)
   (reply : R (alloc.vec.Vec K × Usize))
 | validate (queries : Array U32 22#usize) (reply : R Unit)
 | filled (n : Usize) (value : K)
   (reply : Result (core.result.Result (alloc.vec.Vec K) aspis_core.r0.Error))

'''
header += 'def recordRaw (n : Usize) (reader : verifier.Reader) : NJU_Log.Run Event (Array U8 n × verifier.Reader) :=\n NJU_Log.record (.raw n reader) (NJC_ConcreteUnwrap.raw n reader)\ndef recordK (reader : verifier.Reader) : NJU_Log.Run Event (core.result.Result K verifier.Error × verifier.Reader) :=\n NJU_Log.record (.k reader) (NIL_FreshOps.readK reader)\ndef recordE (reader : verifier.Reader) : NJU_Log.Run Event (core.result.Result E verifier.Error × verifier.Reader) :=\n NJU_Log.record (.e reader) (NIL_FreshOps.readE reader)\ndef recordSemantic (bytes : Slice U8) (cursor : Usize) : NJU_Log.Run Event (core.result.Result (Array K 10#usize × Usize) verifier.Error) :=\n NJU_Log.record (.semantic bytes cursor) (NIL_FreshOps.semantic bytes cursor)\ndef recordWeights (bytes : Slice U8) (cursor : Usize) (weights : alloc.vec.Vec K) : NJU_Log.Run Event (core.result.Result (alloc.vec.Vec K × Usize) verifier.Error) :=\n NJU_Log.record (.weights bytes cursor weights) (NIL_FreshOps.weights bytes cursor weights)\ndef recordValidate (queries : Array U32 22#usize) : NJU_Log.Run Event (core.result.Result Unit verifier.Error) :=\n NJU_Log.record (.validate queries) (NJC_ValidateEmission.verifier.validate_checkpoint_queries queries)\ndef recordFilled (r : NP6_StdModel.Reservation) (copy : core.marker.Copy K) (n : Usize) (value : K) :\n NJU_Log.Run Event (core.result.Result (alloc.vec.Vec K) aspis_core.r0.Error) :=\n NJU_Log.record (.filled n value) (NIL_FreshOps.filled (NJC_FilledClause.reserved r) copy n value)\ndef recordAny {F : Type} (inst : core.ops.function.FnMut F U8 Bool) (it : core.slice.iter.Iter U8) (f : F) :\n NJU_Log.Run Event (Bool × core.slice.iter.Iter U8) :=\n NJU_Log.record (.headerAny it) (NIL_FreshOps.any inst it f)\ndef recordDigest {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (hash : H) (chunks : Slice (Slice U8)) :\n NJU_Log.Run Event (Array U8 32#usize) :=\n NJU_Log.record (.digest chunks) ((NIL_FreshOps.digest d).digest hash chunks)\n\n'
footer='end NJU_ResumeObserved\n'
(E/'NJU_ResumeObserved.lean').write_text(header+body+footer)
(E/'NJU_RESUME_TRANSFORM.json').write_text(json.dumps(dict(input=path,sha256=hashlib.sha256(s.encode()).hexdigest(),extraction_runs=0,substitutions=subs,source_slice_sha256=hashlib.sha256(s[a:b].encode()).hexdigest()),indent=2)+'\n')
