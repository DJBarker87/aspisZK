from pathlib import Path
root=Path(__file__).resolve().parents[2]
s='''import R1Z.PV_RunJoin_LayoutPieces43
import R1Z.PV_RunJoin_CanonicalAppend43
import R1Z.PV_RunJoin_ZeroComplete43
import R1Z.PV_RunJoin_RoundComplete43
import R1Z.PV_RunJoin_CloneBytes43
import R1Z.PV_RunJoin_ClaimCanonical41
import R1Z.PV_RunJoin_EndpointCanonical41
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CallerDomain43
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_ResultPost41
variable [ExternalTypes]
abbrev Q := aspis_core.field.QM31

theorem post (ops : ExternalFuns) {H T1 T2 : Type}
    (hash : aspis_core.digest.Digest32 H)
    (helperInst : core.ops.function.FnOnce T1 (Q × Q)
      (core.result.Result (alloc.vec.Vec Q) r1_wire.Error))
    (commitInst : host_semantic.Commitments T2)
    (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (c1 : Array (alloc.vec.Vec aspis_core.field.M31) 26#usize)
    (d g padding : Array Q 1024#usize) (helper : T1) (commitments : T2)
    (initialHash : H) (variant : transport.Variant) :
    Post (fun next : (core.result.Result (host_semantic.BuiltSemantics H) r1_wire.Error) × T2 =>
      match next.1 with
      | .Err _ => True
      | .Ok built => ∃ records, PV_RunJoin_SemanticDomain40.Domain ops
          (alloc.vec.Vec.deref built.bytes) 27#u8 32#usize 0#u8 records)
      (@host_semantic.build_with_helper_mode _ (ProverRwP6BodyCandidate.selected ops)
        H T1 T2 hash helperInst commitInst public1 c1 d g padding helper commitments initialHash variant) := by
  letI : ExternalFuns := ProverRwP6BodyCandidate.selected ops
  unfold host_semantic.build_with_helper_mode
'''
indent=2
lines=[]
def emit(t):
 for l in t.splitlines():lines.append(' '*indent+l)
def simplify():emit('try simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,lift,Aeneas.Std.uncurry,bind_assoc_eq]')
def bind(name):
 emit('apply PV_RunJoin_ResultPost41.bind\nintro '+name)
def good(name,value):
 global indent
 emit('cases '+name+' with\n| Err error => trivial\n| Ok '+value+' =>');indent+=2;simplify()
def pair(name,r,t):
 bind(name);emit(f'rcases {name} with ⟨{r},{t}⟩')
def triple(name,r,t,o):
 bind(name);emit(f'rcases {name} with ⟨{r},{t},{o}⟩')
def row(num,tag,size,t,o,newt,newo,payload,plen):
 emit(f'''have rp := PV_RunJoin_RecordPost43.append ops hash {num}#u8 {tag}#u8 {size}#usize
  ({payload}) {t} {o} (PV_RunJoin_RowShapes41.row{num} ops) ({plen})
  (by change {o}.length+5+{size}≤Usize.max;rw [l{o}];scalar_tac)
apply PV_RunJoin_RecordAppend41.bind_post rp
intro triple{num} hp{num}
rcases triple{num} with ⟨status{num},{newt},{newo}⟩''')
 good('status'+str(num),'challenge'+str(num))
 emit(f'obtain ⟨head{num},headlen{num},hbytes{num},l{newo}⟩ := hp{num}')
 emit(f'have l{newo} : {newo}.length={int(size)+5+({0:32,1:37,2:42,13:129}[num])} := by\n  rw [l{o}] at l{newo}\n  exact l{newo}')
# Parse/control-flow only; the payload association remains through the named postconditions.
bind('checked');good('checked','checkedValue')
pair('committed','rootResult','commit1');good('rootResult','root1')
bind('publicBytes');bind('mappedPublic');good('mappedPublic','pubBytes')
bind('newTranscript');good('newTranscript','t0')
simplify()
emit('''obtain ⟨b0,hb0,vb0⟩ := PV_RunJoin_CloneBytes43.complete (Array.to_slice root1)
rw [hb0]
try simp only [bind_tc_ok,lift]
have lb0 : b0.length=32 := by
  change b0.val.length=32
  rw [vb0]
  exact root1.property''')
row(0,0,0,'t0','b0','t1','b1','Array.to_slice (Std.Array.empty U8)','rfl')
row(1,0,0,'t1','b1','t2','b2','Array.to_slice (Std.Array.empty U8)','rfl')
bind('helperResult');good('helperResult','helperValues')
simplify()
pair('padded','paddingResult','paddedSlice');bind('mappedPadding');good('mappedPadding','paddingValue')
emit('split\n· trivial\n·');indent+=2
bind('helperSum');bind('zero');bind('sumDifferent')
emit('cases sumDifferent with\n| true => trivial\n| false =>');indent+=2;simplify()
pair('committed2','root2Result','commit2');good('root2Result','root2')
row(2,1,32,'t2','b2','t3','b3','Array.to_slice root2','by rw [Array.length_to_slice];rfl')
emit('''have zp := PV_RunJoin_ZeroComplete43.post ops hash t3 b3
  (by rw [lb3];scalar_tac)
apply PV_RunJoin_RecordAppend41.bind_post zp
intro zeroRows hz
rcases zeroRows with ⟨zeroResult,t4,b4⟩''')
good('zeroResult','zc')
emit('have lb4 : b4.length=129 := by\n  have h := PV_RunJoin_ByteExtension43.length hz\n  change b4.val.length=129\n  rw [show b3.val.length=79 from lb3] at h\n  exact h')
row(13,0,0,'t4','b4','t5','b5','Array.to_slice (Std.Array.empty U8)','rfl')
bind('columns');bind('dc');bind('maskSum');bind('maskSum1')
emit('''rw [PV_RunJoin_PolyCell38.embed ops maskSum1]
try simp only [bind_tc_ok]
rw [PV_RunJoin_FlatBytes35.installed ops (PV_RunJoin_PolyCell38.wide maskSum1)]
try simp only [bind_tc_ok,lift]
have mp := PV_RunJoin_CanonicalAppend43.post ops hash 14#u8 3#u8 32#usize
  (Array.to_slice (PV_RunJoin_FlatBytes35.wire (PV_RunJoin_PolyCell38.wide maskSum1))) t5 b5
  (PV_RunJoin_RowShapes41.row14 ops) rfl (by rw [lb5];scalar_tac)
  (PV_RunJoin_HighCell41.high maskSum1)
apply PV_RunJoin_RecordAppend41.bind_post mp
intro maskRecord hm
rcases maskRecord with ⟨maskResult,t6,b6⟩''')
good('maskResult','eta')
emit('''have lb6 : b6.length=171 := by
  have h := PV_RunJoin_CanonicalRecord43.length hm
  change b6.val.length=171
  rw [show b5.val.length=134 from lb5] at h
  exact h
apply PV_RunJoin_RecordAppend41.bind_post
  (PV_RunJoin_RoundComplete43.post ops hash _ _ t6 b6 maskSum1 (by rw [lb6];scalar_tac))
intro sumcheck hs
rcases sumcheck with ⟨sumcheckResult,t7,b7⟩''')
good('sumcheckResult','pointRunning')
emit('rcases pointRunning with ⟨alpha,running⟩')
emit("""change PV_RunJoin_RoundStream43.Stream b6.val 10 b7.val at hs
have lb7 : b7.length=9181 := by
  have h := PV_RunJoin_RoundStream43.length hs
  change b7.val.length=9181
  rw [show b6.val.length=171 from lb6] at h
  exact h""")
bind('claimsResult');good('claimsResult','claims')
bind('stateBefore');bind('alpha8');bind('alpha9');bind('extras')
emit("""obtain ⟨claimBytes,hclaim,claimLen,claimHigh⟩ := PV_RunJoin_ClaimCanonical41.encode ops claims extras
rw [hclaim]
try simp only [bind_tc_ok]
""")
def circle_record(num,payload,plen,phigh,oldout,newout,oldt,newt,z):
 global indent
 size={25:3712,26:928}[num]
 emit(f"""obtain ⟨header{num},framed{num},hlen{num},fb{num},fp{num}⟩ :=
  PV_RunJoin_RecordFrame41.frame ops {num}#u8 {num-21}#u8 {size}#usize
    (alloc.vec.Vec.deref {payload}) (PV_RunJoin_RowShapes41.row{num} ops) {plen} (by scalar_tac)
apply PV_RunJoin_RecordAppend41.bind_post fp{num}
intro recorded{num} hr{num}""")
 good('recorded'+str(num),'recordValue'+str(num))
 emit(f"""change recordValue{num}=framed{num} at hr{num}
subst recordValue{num}""");simplify()
 pair('circle'+str(num),'circleResult'+str(num),newt)
 good('circleResult'+str(num),z)
 emit(f"""have fl{num} : framed{num}.length=5+{size} := by
  change framed{num}.val.length=5+{size}
  rw [fb{num},List.length_append,hlen{num}]
  exact congrArg (fun n => 5+n) {plen}
obtain ⟨{newout},hext{num},vext{num}⟩ := PV_RunJoin_ByteAppend38.append {oldout}
  (alloc.vec.Vec.deref framed{num})
  (by change {oldout}.length+framed{num}.length≤Usize.max;rw [l{oldout},fl{num}];scalar_tac)
rw [hext{num}]
try simp only [bind_tc_ok]
have piece{num} : PV_RunJoin_CanonicalRecord43.Piece {size} {oldout}.val {newout}.val := by
  refine ⟨header{num},{payload}.val,hlen{num},{plen},{phigh},?_⟩
  rw [vext{num}]
  change {oldout}.val++framed{num}.val={oldout}.val++header{num}++{payload}.val
  change framed{num}.val=header{num}++{payload}.val at fb{num}
  rw [fb{num},List.append_assoc]
have l{newout} : {newout}.length={ {25:12898,26:13831}[num]} := by
  have h := PV_RunJoin_CanonicalRecord43.length piece{num}
  change {newout}.val.length={ {25:12898,26:13831}[num]}
  rw [show {oldout}.val.length={ {25:9181,26:12898}[num]} from l{oldout}] at h
  exact h""")
circle_record(25,'claimBytes','claimLen','claimHigh','b7','b8','t7','t8','z0')
emit("""apply PV_RunJoin_RecordAppend41.bind_post (PV_RunJoin_EndpointCanonical41.post ops columns variant z0)
intro endpointBytes ep
obtain ⟨endpointLen,endpointHigh⟩ := ep""")
circle_record(26,'endpointBytes','endpointLen','endpointHigh','b8','b9','t8','t9','z1')
bind('equalPoints')
emit('cases equalPoints with\n| true => trivial\n| false =>');indent+=2
emit("""exact PV_RunJoin_LayoutPieces43.domain ops (alloc.vec.Vec.deref b9)
  b5.val b6.val b7.val b8.val lb5 hm hs piece25 piece26""")
s+='\n'.join(lines)+'\n#print axioms post\nend R1Z.PV_RunJoin_CallerDomain43\n'
(root/'docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_CallerDomain43.lean').write_text(s)
