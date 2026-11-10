#!/usr/bin/env python3
# PCVZ_ generator: update_residue_row_loop1 (+ .body) result-projection refinement from the P1n n3b module.
import sys,re
inp,out=sys.argv[1:3]
src=open(inp).read()
src=src.replace('import Aeneas\n','import Aeneas\nimport PRVEq_P3W_LoopMap\n',1)
F='NEI_PushRaw.PRVFresh_NEI_PushRaw_Funs_n3.verifier';G='NEI_PushRaw';PE='PRVEq.NEI_PushRaw.Funs_n3.verifier'
for pat in (r'update_residue_row_loop1\.body',r'update_residue_row_loop1'):
    m=re.search(r'/- PRV-OBLIGATION \(semantic; P3\): PRVEq\.NEI_PushRaw\.Funs_n3\.verifier\.'+pat+r' :.*?-/\n\n?',src,re.S)
    assert m,pat
    src=src[:m.start()]+('@@BODY@@' if 'body' in pat else '@@LOOP@@')+src[m.end():]
body=f'''-- RESULT-PROJECTION REFINEMENT (not constant equality): the gate's loop body returns ControlFlow (state) (back) while the
-- frozen emission returns ControlFlow (state) (iter, back); the types differ, so `@fresh = @gate` is ill-typed.
-- Proved: gate body = fresh body with the done payload projected to its second component; gate loop1 = fresh loop1 projected.
set_option maxHeartbeats 200000 in
theorem {PE}.update_residue_row_loop1.body_proj (iter : core.slice.iter.IterMut Std.U64)
    (back : core.slice.iter.IterMut Std.U64 → core.slice.iter.IterMut Std.U64) :
    {G}.update_residue_row_loop1.body iter back
      = (do let cf ← {F}.update_residue_row_loop1.body iter back; ok (PRVEq_P3W.mapCF Prod.snd cf)) := by
  have hsh : ∀ x : Std.U64, x >>> 31#i32 = x >>> 31#u32 := fun _ => rfl
  unfold {F}.update_residue_row_loop1.body {G}.update_residue_row_loop1.body
  rcases hn : core.slice.iter.IteratorIterMut.next iter with p | e | _
  · obtain ⟨o, iter1, nb⟩ := p
    cases o with
    | none => simp [PRVEq_P3W.mapCF]
    | some limb =>
      simp [hsh, PRVEq_P3W.mapCF]
  · simp
  · simp
#print axioms {PE}.update_residue_row_loop1.body_proj

'''
loop=f'''set_option maxHeartbeats 200000 in
theorem {PE}.update_residue_row_loop1.loop_proj (iter : core.slice.iter.IterMut Std.U64)
    (back : core.slice.iter.IterMut Std.U64 → core.slice.iter.IterMut Std.U64) :
    {G}.update_residue_row_loop1 iter back
      = (do let p ← {F}.update_residue_row_loop1 iter back; ok p.2) := by
  have hl := PRVEq_P3W.loop_map (fun (iter1, back1) => {F}.update_residue_row_loop1.body iter1 back1)
    (fun (iter1, back1) => {G}.update_residue_row_loop1.body iter1 back1) Prod.snd
    (fun p => by obtain ⟨a, b⟩ := p; exact {PE}.update_residue_row_loop1.body_proj a b) (iter, back)
  unfold {F}.update_residue_row_loop1 {G}.update_residue_row_loop1
  rw [hl]
  generalize (loop (fun (iter1, back1) => {F}.update_residue_row_loop1.body iter1 back1) (iter, back)) = r
  cases r <;> rfl
#print axioms {PE}.update_residue_row_loop1.loop_proj

'''
src=src.replace('@@BODY@@',body).replace('@@LOOP@@',loop)
open(out,'w').write(src)
