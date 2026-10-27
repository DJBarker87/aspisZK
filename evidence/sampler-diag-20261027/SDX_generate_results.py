from pathlib import Path
E=Path(__file__).resolve().parent
for tag,ws,bs,digit,q in [('P',[2147483647]+[0]*7,[255,255,255,127]+[0]*28,0,2147483647),('Zero',[0]*8,[0]*32,0,0),('P1',[2147483648]+[0]*7,[0,0,0,128]+[0]*28,1,2147483648),('FF',[4294967295]*8,[255]*32,255,4294967295)]:
 arr=lambda xs,typ:'['+','.join(str(x)+'#'+typ for x in xs)+']'
 t=f'''import SDX_{tag}
import AdapterRwScalar
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace SDX_{tag}Result
open SDX_Common SDX_{tag} AspisR1.AdapterRw.Scalar

def block : Array U8 32#usize := ⟨{arr(bs,'u8')},by simp⟩
def rank : Array U32 8#usize := ⟨{arr(ws,'u32')},by simp⟩
def digits : Array U32 8#usize := ⟨List.replicate 8 {digit}#u32,by simp⟩
abbrev word := SDX_Join_Release.sampler.low_base_p_digits.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
abbrev seedFn := SDX_Join_Release.sampler.low_base_p_digits.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32
abbrev callback := SDX_Join_Release.sampler.low_base_p_digits.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
abbrev fn := SDX_Join_Release.sampler.low_base_p_digits.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32
'''
 for i in range(8):
  t+=f'''\ntheorem word{i} : word block {i}#usize = ok ({ws[i]}#u32,block) := by
  unfold word SDX_Join_Release.sampler.low_base_p_digits.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
  have hm : 4#usize * {i}#usize = ok {4*i}#usize := mul_eq _ _ _ rfl
  have ha : {4*i}#usize + 4#usize = ok {4*i+4}#usize := add_eq _ _ _ rfl
  rw [hm,bind_tc_ok,ha,bind_tc_ok]
  rfl
#print axioms word{i}
'''
 for i in reversed(range(8)):
  t+=f'''\ntheorem seed{i} : core.array.fromFnList seedFn {8-i} {i}#usize block = ok ({arr(ws[i:],'u32')},block) := by
  rw [core.array.fromFnList]
'''
  if i==7:
   t+=f'''  change (do let (v,c) ← word block 7#usize; ok ([v],c)) = _
  rw [word7]
  rfl
'''
  else:
   t+=f'''  change (do
    let (v,c) ← word block {i}#usize
    let j ← {i}#usize + 1#usize
    let (xs,c') ← core.array.fromFnList seedFn {7-i} j c
    ok (v::xs,c')) = _
  rw [word{i}]
  change (do
    let j ← {i}#usize + 1#usize
    let (xs,c') ← core.array.fromFnList seedFn {7-i} j block
    ok ({ws[i]}#u32::xs,c')) = _
  have ha : {i}#usize + 1#usize = ok {i+1}#usize := add_eq _ _ _ rfl
  rw [ha,bind_tc_ok,seed{i+1}]
  rfl
'''
  t+=f'#print axioms seed{i}\n'
 t+='''
theorem init : _root_.core.array.from_fn 8#usize seedFn block = ok rank := by
  have h8 : (8#usize).val = 8 := by scalar_tac
  unfold _root_.core.array.from_fn
  have hs : core.array.fromFnList seedFn (8#usize).val 0#usize block = ok (rank.val,block) := by
    simpa only [h8,rank] using seed0
  rw [hs]
  change (if h : rank.val.length = (8#usize).val then ok (⟨rank.val,h⟩ : Array U32 8#usize) else fail .panic) = _
  rw [dif_pos rank.property]
  rfl
#print axioms init
'''
 t+=f'''
theorem division (i : Usize) : callback rank i = ok ({digit}#u32,rank,id) := by
  unfold callback SDX_Join_Release.sampler.low_base_p_digits.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
  change (do
    let (rem,back) ← loop step (st8,id,0#u64)
    let d ← lift (UScalar.cast .U32 rem)
    ok (d,Array.from_slice rank (back st8).iter.slice,id)) = _
  rw [loop8]
  change ok ({digit}#u32,Array.from_slice rank ((fin8 id) st8).iter.slice,id) = _
'''
 for n in range(9,17):t+=f'  have h{n} : {n} ≤ Usize.max := by scalar_tac\n'
 t+='  simp ['+','.join(['fin'+str(n) for n in range(9)]+['st'+str(n) for n in range(9)]+['restore','mk','rank','Array.from_slice']+['h'+str(n) for n in range(9,17)])+']\n#print axioms division\n'
 t+=f'''
theorem callback_state (i : Usize) : fn.call_mut rank i = ok ({digit}#u32,rank) := by
  unfold fn SDX_Join_Release.sampler.low_base_p_digits.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32
  change (do let (v,c,restore) ← callback rank i; ok (v,restore c)) = _
  rw [division i]
  rfl
#print axioms callback_state

theorem eight_digits : SDX_Join_fromFnState 8#usize fn rank = ok (digits,rank) := by
  have h := constant fn rank {digit}#u32 callback_state 8 0#usize (by scalar_tac)
  unfold SDX_Join_fromFnState
  change (do
    let (xs,c) ← core.array.fromFnList fn 8 0#usize rank
    dite (xs.length = 8) (fun h => ok ((⟨xs,h⟩ : Array U32 8#usize),c)) (fun _ => fail .panic)) = _
  rw [h]
  rfl
#print axioms eight_digits

theorem emitted : SDX_Join_Release.sampler.low_base_p_digits block = ok (digits,{q}#u32) := by
  unfold SDX_Join_Release.sampler.low_base_p_digits
  rw [init]
  change (do
    let (ds,c) ← SDX_Join_fromFnState 8#usize fn rank
    let q ← Array.index_usize c 0#usize
    ok (ds,q)) = _
  rw [eight_digits]
  rfl
#print axioms emitted
end SDX_{tag}Result
'''
 E.joinpath(f'SDX_{tag}Result.lean').write_text(t)
