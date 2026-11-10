#!/usr/bin/env python3
# PCVZ_ generator: build PRVEq_<M>_p3w.lean from the P1n n3b equality module by replacing the Q.raw obligation with a proof.
import sys,re
mod,gate,fresh,suffix,out=sys.argv[1:6]
PFX=sys.argv[7] if len(sys.argv)>7 else f'PRVEq.{gate}.{suffix}'   # e.g. AspisR1CanonicalQRawUnified.Funs  AspisR1CanonicalQRawUnified  PRVFresh_..._n3  Funs_n3
src=open(sys.argv[6]).read()
F=f'{gate}.{fresh}.fast_pairing.canonical'
G=f'{gate}.canonical'
T=f'PRVEq.{gate}.{suffix}.fast_pairing.canonical'
PE=PFX+'.fast_pairing.canonical'
src=src.replace('import Aeneas\n','import Aeneas\nimport PRVEq_P3W_ArrayMap\n',1)
m=re.search(r'/- PRV-OBLIGATION \(semantic; P3\): PRVEq\.[^\n]*fast_pairing\.canonical\.Q\.raw :.*?-/\n',src,re.S)
assert m
proof=f'''set_option maxHeartbeats 200000 in
theorem {PE}.Q.raw.closure_call : ∀ c x, @{F}.Q.raw.closure.Insts.CoreOpsFunctionFnTupleU64U64.call c x = @{G}.Q.raw.closure_2.Insts.CoreOpsFunctionFnTupleU64U64.call c x := by
  intro c x
  unfold {F}.Q.raw.closure.Insts.CoreOpsFunctionFnTupleU64U64.call {G}.Q.raw.closure_2.Insts.CoreOpsFunctionFnTupleU64U64.call
  simp only [{PE}.P]
  rfl
#print axioms {PE}.Q.raw.closure_call

set_option maxHeartbeats 200000 in
theorem {PE}.Q.raw : @{F}.Q.raw = @{G}.Q.raw := by
  funext self rhs
  have hm1 := PRVEq_P3W.map_pure {G}.Q.raw.closure.Insts.CoreOpsFunctionFnMutTupleU32U64 core.convert.num.FromU64U32.from (fun c x => rfl) self ()
  have hm2 := PRVEq_P3W.map_pure {G}.Q.raw.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U64 core.convert.num.FromU64U32.from (fun c x => rfl) rhs ()
  unfold {F}.Q.raw {G}.Q.raw
  simp only [hm1, hm2, bind_tc_ok, Aeneas.Std.lift, PRVEq_P3W.idx_mapArr, PRVEq_P3W.idx_make4_0, PRVEq_P3W.idx_make4_1,
    PRVEq_P3W.idx_make4_2, PRVEq_P3W.idx_make4_3, {PE}.Q.raw.closure_call, {PE}.Q.raw.PP, {PE}.P]
  all_goals rfl
#print axioms {PE}.Q.raw

'''
src=src[:m.start()]+proof+src[m.end():]
open(out,'w').write(src)
