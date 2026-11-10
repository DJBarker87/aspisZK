#!/usr/bin/env python3
# PCVZ_ generator: Dot.finish equality (Array.map with effectful constant-state callback) from the P1n n3b module.
import sys,re
gate,fresh,pfx,out,inp=sys.argv[1:6]
src=open(inp).read()
F=f'{gate}.{fresh}.fast_pairing.canonical';G=f'{gate}.canonical';PE=pfx+'.fast_pairing.canonical'
src=src.replace('import Aeneas\n','import Aeneas\nimport PRVEq_P3W_ArrayMap\nimport PRVEq_P3W_ArrayMapMon\n',1)
m=re.search(r'/- PRV-OBLIGATION \(semantic; P3\): PRVEq\.[^\n]*fast_pairing\.canonical\.Dot\.finish :.*?-/\n',src,re.S)
assert m
proof=f'''set_option maxHeartbeats 200000 in
theorem {PE}.Dot.finish : @{F}.Dot.finish = @{G}.Dot.finish := by
  have hr : ∀ x, {F}.reduce x = {G}.reduce x := fun x => congrFun {PE}.reduce x
  funext self
  obtain ⟨x0, x1, x2, x3, h⟩ := PRVEq_P3W.arr4 self.sums
  unfold {F}.Dot.finish {G}.Dot.finish
  rw [h, PRVEq_P3W.map4_mon (BuiltinFnMut Std.U64 Std.U32) {G}.reduce {G}.reduce
    (by intro x; first | rfl | simp [BuiltinFnMut]) x0 x1 x2 x3]
  simp only [PRVEq_P3W.idx_make4_0, PRVEq_P3W.idx_make4_1, PRVEq_P3W.idx_make4_2, PRVEq_P3W.idx_make4_3, hr]
  all_goals rfl
#print axioms {PE}.Dot.finish

'''
src=src[:m.start()]+proof+src[m.end():]
open(out,'w').write(src)
