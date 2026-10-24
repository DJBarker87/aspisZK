import Port5Q1_Domain
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port5Q1_Gather
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2
open Port3_NativeGeometryBody
variable {CoreError : Type}

theorem traversal (ops : Ops CoreError) (leaves : Port5Q1_GeometryCanonical.SessionAPrimitives ops)
    (domain : Port5Q1_Domain.SessionADomain ops)
    (start : Usize) (iter : core.slice.iter.Iter U32) (zs flat : alloc.vec.Vec U32)
    (out : verifier.QueryGeometry) (fuel : Nat)
    (remaining : iter.i+fuel=iter.slice.val.length)
    (canonical : ∀ x ∈ flat.val, Port5Q1_GeometryCanonical.Canonical x)
    (raw : ∀ x ∈ flat.val, x≠0#u32)
    (run : verifier.QueryGeometry.for_range_loop0 (Port4C_GeometryStd.install ops)
      iter start zs flat=ok (.Ok out)) :
    ∃ zsFinal flatFinal terminal,
      (∀ x ∈ flatFinal.val, Port5Q1_GeometryCanonical.Canonical x) ∧
      (∀ x ∈ flatFinal.val, x≠0#u32) ∧
      verifier.QueryGeometry.for_range_loop0.body (Port4C_GeometryStd.install ops)
        start terminal zsFinal flatFinal=ok (done (.Ok out)) ∧
      terminal.i=terminal.slice.val.length ∧
      zsFinal.val.length=zs.val.length+fuel ∧ flatFinal.val.length=flat.val.length+5*fuel ∧
      flatFinal.val.map S7JoinBasisMachine.decode=flat.val.map S7JoinBasisMachine.decode++
        (iter.slice.val.drop iter.i).flatMap (fun q => Port5Q1_Domain.words q.val) ∧
      zsFinal.val.map S7JoinBasisMachine.decode=zs.val.map S7JoinBasisMachine.decode++
        (iter.slice.val.drop iter.i).map (fun q => Port5Q1_Domain.lineZ q.val) := by
  induction fuel generalizing iter zs flat with
  | zero =>
    have next : core.slice.iter.IteratorSliceIter.next iter=ok (none,iter) := by
      unfold core.slice.iter.IteratorSliceIter.next
      split
      · rename_i active; change iter.i < iter.slice.val.length at active; omega
      · rfl
    unfold verifier.QueryGeometry.for_range_loop0 at run
    rw [Aeneas.Std.loop.eq_def] at run
    simp only [Aeneas.Std.uncurry] at run
    generalize bodyRun : verifier.QueryGeometry.for_range_loop0.body
      (Port4C_GeometryStd.install ops) start iter zs flat=result at run
    cases result with
    | fail e => cases run
    | div => cases run
    | ok flow =>
      cases flow with
      | cont s =>
        rcases s with ⟨iter1,zs1,flat1⟩
        exact False.elim (Port4C_GeometryControl.terminal_not_cont ops start iter iter iter1
          zs flat zs1 flat1 next bodyRun)
      | done value =>
        cases Result.ok.inj run
        refine ⟨zs,flat,iter,canonical,raw,bodyRun,by omega,by omega,by omega,?_,?_⟩
        · rw [List.drop_eq_nil_of_le (by omega)]; simp
        · rw [List.drop_eq_nil_of_le (by omega)]; simp
  | succ fuel ih =>
    have active : iter.i < iter.slice.val.length := by omega
    let query := iter.slice.val[iter.i]
    let nextIter : core.slice.iter.Iter U32 := {iter with i:=iter.i+1}
    have next : core.slice.iter.IteratorSliceIter.next iter=ok (some query,nextIter) := by
      unfold core.slice.iter.IteratorSliceIter.next
      split
      · rfl
      · rename_i inactive; exact False.elim (inactive active)
    unfold verifier.QueryGeometry.for_range_loop0 at run
    rw [Aeneas.Std.loop.eq_def] at run
    simp only [Aeneas.Std.uncurry] at run
    generalize bodyRun : verifier.QueryGeometry.for_range_loop0.body
      (Port4C_GeometryStd.install ops) start iter zs flat=result at run
    cases result with
    | fail e => cases run
    | div => cases run
    | ok flow =>
      cases flow with
      | done value =>
        cases Result.ok.inj run
        exact False.elim (Port4C_GeometryControl.active_not_done ops start iter nextIter query zs flat out next bodyRun)
      | cont s =>
        rcases s with ⟨iter1,zs1,flat1⟩
        have canon := Port5Q1_GeometryCanonical.step ops leaves start iter nextIter iter1 query zs zs1 flat flat1 canonical next bodyRun
        have meaning := Port5Q1_Domain.gathered_row ops domain start iter nextIter iter1 query
          zs zs1 flat flat1 next bodyRun
        obtain ⟨r,u,parent,left,right,fibre,fleft,fright,point,square,doubled,one,fields⟩ :=
          Port4C_GeometryGather.step ops start iter nextIter iter1 query zs zs1 flat flat1 next bodyRun
        rcases fields with ⟨same,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,rowRaw,append,line⟩
        subst iter1
        have raw1 : ∀ x ∈ flat1.val, x≠0#u32 := by
          intro x hx
          rw [append,List.mem_append] at hx
          exact hx.elim (raw x) (rowRaw x)
        obtain ⟨zf,ff,term,cf,rf,ht,hi,hzl,hfl,hfm,hzm⟩ := ih nextIter zs1 flat1 (by dsimp [nextIter]; omega) canon raw1 run
        refine ⟨zf,ff,term,cf,rf,ht,hi,?_,?_,?_,?_⟩
        · rw [line,List.length_append,List.length_singleton] at hzl; omega
        · rw [append,List.length_append] at hfl
          have len : r.words.length=5 := by simp [Port4C_GeometryGather.Row.words]
          rw [len] at hfl; omega

        · rw [List.drop_eq_getElem_cons active,List.flatMap_cons]
          rw [hfm,meaning.2.1]
          exact List.append_assoc _ _ _
        · rw [List.drop_eq_getElem_cons active,List.map_cons]
          rw [hzm,meaning.2.2]
          exact List.append_assoc _ _ _

#print axioms traversal
end AspisR1.Port5Q1_Gather
end
