import Port5Q1_GeometryTerminal

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port5Q1_GeometryCanonical
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2
open Port3_NativeGeometryBody
variable {CoreError : Type}
def Canonical (x : U32) : Prop := x.val < AspisCircleGroupOrder.P

/-- Primitive domain/field ports only. No geometry, query, state or successful
transaction conclusion is a field. The concrete session A instances remain open. -/
structure SessionAPrimitives (ops : Ops CoreError) : Prop where
  point : ∀ f p, ops.op15 f=ok p → Canonical p.x ∧ Canonical p.y
  line : ∀ f x, ops.op14 f=ok x → Canonical x
  multiply : ∀ x y z, Canonical x → Canonical y → ops.op9 x y=ok z → Canonical z
  double : ∀ x y, Canonical x → ops.op10 x=ok y → Canonical y
  one : ∀ x, ops.op7=ok x → Canonical x
  subtract : ∀ x y z, Canonical x → Canonical y → ops.op8 x y=ok z → Canonical z

theorem field_nonzero (x : U32) (canonical : Canonical x) (raw : x≠0#u32) :
    S7JoinBasisMachine.decode x≠0 := by
  intro zero
  have h := congrArg ZMod.val zero
  change x.val % AspisCircleGroupOrder.P=0 at h
  rw [Nat.mod_eq_of_lt canonical] at h
  exact raw (UScalar.eq_of_val_eq h)

theorem step (ops : Ops CoreError) (leaves : SessionAPrimitives ops) (start : Usize)
    (iter iter1 iterOut : core.slice.iter.Iter U32) (query : U32)
    (zs zsOut flat flatOut : alloc.vec.Vec U32)
    (canonical : ∀ x ∈ flat.val, Canonical x)
    (next : core.slice.iter.IteratorSliceIter.next iter=ok (some query,iter1))
    (run : verifier.QueryGeometry.for_range_loop0.body (Port4C_GeometryStd.install ops)
      start iter zs flat=ok (cont (iterOut,zsOut,flatOut))) :
    ∀ x ∈ flatOut.val, Canonical x := by
  obtain ⟨r,u,parent,left,right,fibre,fleft,fright,point,square,doubled,one,fields⟩ :=
    Port4C_GeometryGather.step ops start iter iter1 iterOut query zs zsOut flat flatOut next run
  rcases fields with ⟨_,_,_,pointRun,_,_,_,lineX,_,_,lineY,hx,hy,mul,dbl,unit,sub,_,append,_⟩
  have cp := leaves.point _ _ pointRun
  have cx := leaves.line _ _ lineX
  have cy := leaves.line _ _ lineY
  have cz := leaves.subtract _ _ _ (leaves.double _ _ (leaves.multiply _ _ _ cx cx mul) dbl)
    (leaves.one _ unit) sub
  intro x member
  rw [append,List.mem_append] at member
  rcases member with member | member
  · exact canonical x member
  · simp only [Port4C_GeometryGather.Row.words,List.mem_cons,List.mem_singleton] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · rw [hx]; exact cp.1
    · rw [hy]; exact cp.2
    · exact cx
    · exact cy
    · exact cz

/-- Canonicality is propagated through the ACTUAL gather traversal to its
terminal flat buffer, rather than supplied as an accepted-loop postcondition. -/
theorem traversal (ops : Ops CoreError) (leaves : SessionAPrimitives ops)
    (start : Usize) (iter : core.slice.iter.Iter U32) (zs flat : alloc.vec.Vec U32)
    (out : verifier.QueryGeometry) (fuel : Nat)
    (remaining : iter.i+fuel=iter.slice.val.length)
    (canonical : ∀ x ∈ flat.val, Canonical x)
    (run : verifier.QueryGeometry.for_range_loop0 (Port4C_GeometryStd.install ops)
      iter start zs flat=ok (.Ok out)) :
    ∃ zsFinal flatFinal terminal,
      (∀ x ∈ flatFinal.val, Canonical x) ∧
      verifier.QueryGeometry.for_range_loop0.body (Port4C_GeometryStd.install ops)
        start terminal zsFinal flatFinal=ok (done (.Ok out)) ∧
      terminal.i=terminal.slice.val.length ∧
      zsFinal.val.length=zs.val.length+fuel ∧ flatFinal.val.length=flat.val.length+5*fuel := by
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
        exact ⟨zs,flat,iter,canonical,bodyRun,by omega,by omega,by omega⟩
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
        have canon := step ops leaves start iter nextIter iter1 query zs zs1 flat flat1 canonical next bodyRun
        obtain ⟨r,_,_,_,_,_,_,_,_,_,_,fields⟩ :=
          Port4C_GeometryGather.step ops start iter nextIter iter1 query zs zs1 flat flat1 next bodyRun
        have same := fields.1
        subst iter1
        have append := fields.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        have line := fields.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
        obtain ⟨zf,ff,term,cf,ht,hi,hzl,hfl⟩ := ih nextIter zs1 flat1 (by dsimp [nextIter]; omega) canon run
        refine ⟨zf,ff,term,cf,ht,hi,?_,?_⟩
        · rw [line,List.length_append,List.length_singleton] at hzl; omega
        · rw [append,List.length_append] at hfl
          have len : r.words.length=5 := by simp [Port4C_GeometryGather.Row.words]
          rw [len] at hfl; omega

#print axioms field_nonzero
#print axioms step
#print axioms traversal
end AspisR1.Port5Q1_GeometryCanonical
end
