import NFN_GeometryPart08
set_option autoImplicit false
namespace AspisR1.NNG_GeometryLineCanonical094
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2
open Port3_NativeGeometryBody
/-- A symbolic gather invariant: line_z is copied from the fifth reduced
word of each SAME successful row. No concrete geometry is normalized. -/
theorem traversal {CoreError : Type} (ops : Ops CoreError)
 (leaves : Port5Q1_GeometryCanonical.SessionAPrimitives ops)
 (start : Usize) (iter : core.slice.iter.Iter U32) (zs flat : alloc.vec.Vec U32)
 (out : verifier.QueryGeometry) (fuel : Nat)
 (remaining : iter.i+fuel=iter.slice.val.length)
 (canonical : ∀ x∈flat.val,Port5Q1_GeometryCanonical.Canonical x)
 (lines : ∀ x∈zs.val,Port5Q1_GeometryCanonical.Canonical x)
 (run : verifier.QueryGeometry.for_range_loop0 (Port4C_GeometryStd.install ops)
  iter start zs flat=ok (.Ok out)) :
 ∀ x∈out.line_z.val,Port5Q1_GeometryCanonical.Canonical x := by
 induction fuel generalizing iter zs flat with
 | zero=>
   have next : core.slice.iter.IteratorSliceIter.next iter=ok (none,iter) := by
    unfold core.slice.iter.IteratorSliceIter.next
    split
    · rename_i active;change iter.i < iter.slice.val.length at active;omega
    · rfl
   unfold verifier.QueryGeometry.for_range_loop0 at run
   rw [Aeneas.Std.loop.eq_def] at run
   simp only [Aeneas.Std.uncurry] at run
   generalize bodyRun : verifier.QueryGeometry.for_range_loop0.body
    (Port4C_GeometryStd.install ops) start iter zs flat=result at run
   cases result with
   | fail e=>cases run
   | div=>cases run
   | ok flow=>
     cases flow with
     | cont s=>
       rcases s with ⟨iter1,zs1,flat1⟩
       exact False.elim (Port4C_GeometryControl.terminal_not_cont ops start iter iter iter1
        zs flat zs1 flat1 next bodyRun)
     | done value=>
       cases Result.ok.inj run
       have fields := Port4C_GeometryControl.terminal_fields ops start iter iter zs flat out next bodyRun
       rw [fields.2]
       exact lines
 | succ fuel ih=>
   have active : iter.i < iter.slice.val.length := by omega
   let query := iter.slice.val[iter.i]
   let nextIter : core.slice.iter.Iter U32 := {iter with i:=iter.i+1}
   have next : core.slice.iter.IteratorSliceIter.next iter=ok (some query,nextIter) := by
    unfold core.slice.iter.IteratorSliceIter.next
    split
    · rfl
    · rename_i inactive;exact False.elim (inactive active)
   unfold verifier.QueryGeometry.for_range_loop0 at run
   rw [Aeneas.Std.loop.eq_def] at run
   simp only [Aeneas.Std.uncurry] at run
   generalize bodyRun : verifier.QueryGeometry.for_range_loop0.body
    (Port4C_GeometryStd.install ops) start iter zs flat=result at run
   cases result with
   | fail e=>cases run
   | div=>cases run
   | ok flow=>
     cases flow with
     | done value=>
       cases Result.ok.inj run
       exact False.elim (Port4C_GeometryControl.active_not_done ops start iter nextIter query zs flat out next bodyRun)
     | cont s=>
       rcases s with ⟨iter1,zs1,flat1⟩
       have canonical1 := Port5Q1_GeometryCanonical.step ops leaves start iter nextIter iter1 query
        zs zs1 flat flat1 canonical next bodyRun
       obtain ⟨r,u,parent,left,right,fibre,fleft,fright,point,square,doubled,one,fields⟩ :=
        Port4C_GeometryGather.step ops start iter nextIter iter1 query zs zs1 flat flat1 next bodyRun
       rcases fields with ⟨same,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,append,line⟩
       subst iter1
       have lines1 : ∀ x∈zs1.val,Port5Q1_GeometryCanonical.Canonical x := by
        intro x member
        rw [line,List.mem_append,List.mem_singleton] at member
        rcases member with old | equal
        · exact lines x old
        · subst x
          apply canonical1 r.lineZ
          rw [append,List.mem_append]
          exact Or.inr (by simp [Port4C_GeometryGather.Row.words])
       exact ih nextIter zs1 flat1 (by dsimp [nextIter];omega) canonical1 lines1 run
#print axioms traversal
end AspisR1.NNG_GeometryLineCanonical094
