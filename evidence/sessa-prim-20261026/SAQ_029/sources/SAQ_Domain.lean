import SAQ_Geometry
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAQ_Domain
open Aeneas Aeneas.Std Result

theorem array_bound {T : Type} {n : Usize} (a : Array T n) (i : Usize) (x : T)
    (run : Array.index_usize a i=ok x) : i.val<n.val := by
  by_contra bad
  have absent : a.val[i.val]?=none := List.getElem?_eq_none (by have := a.property; omega)
  simp only [Array.index_usize,absent] at run
  cases run

/-- The successful high-table read proves the original 18-bit input bound;
no independently supplied valid-index hypothesis is needed. -/
theorem point_bound (u : Usize)
    (p : AspisR1QueryGeometryActual.domain.Point U32)
    (run : AspisR1QueryGeometryActual.fast_domain.fibre_point
      R17CurrentCM31Semantics.operations u=ok p) : u.val<262144 := by
  unfold AspisR1QueryGeometryActual.fast_domain.fibre_point at run
  obtain ⟨index,get,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  have same : u=index := Result.ok.inj get
  subst index
  obtain ⟨lo,_,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨a,_,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨left,_,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨hi,shift,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b,lookup,_⟩ := Port3_PushFrame.bind_success _ _ _ run
  have hb : hi.val<512 := array_bound _ _ _ lookup
  have hn0 : 0≤(9#i32).val := by decide
  have hn1 : (9#i32).val<UScalarTy.Usize.numBits := by
    cases System.Platform.numBits_eq <;> norm_num [UScalarTy.Usize_numBits_eq,*]
  obtain ⟨out,ho,⟨hv,_⟩⟩ := WP.spec_imp_exists (UScalar.ShiftRight_IScalar_spec u (9#i32) hn0 hn1)
  have eq : out=hi := Result.ok.inj (ho.symm.trans shift)
  subst out
  have value : hi.val=u.val/512 := by
    rw [hv]
    simp [IScalar.toNat,Nat.shiftRight_eq_div_pow]
  rw [value] at hb
  omega

theorem point {C : Type} (ops : Port3_NativeGeometryBody.Ops C) (u : Usize)
    (p : SAQ_Geometry.Point) (run : (SAQ_Geometry.install ops).op15 u=ok p) :
    S7JoinBasisMachine.decode p.x=AspisCircleTensorBinding.X
      (FoldStoredGeometry.sourceFibre (Port5Q1_Domain.index u.val)) ∧
    S7JoinBasisMachine.decode p.y=(FoldStoredGeometry.sourceFibre (Port5Q1_Domain.index u.val)).1.2 := by
  obtain ⟨out,ho,he⟩ := Port3_PushFrame.bind_success _ _ _ run
  have same : (⟨out.x,out.y⟩ : SAQ_Geometry.Point)=p := Result.ok.inj he
  subst p
  have bound := point_bound u out ho
  have stored := R17CurrentDomainSource.successful_fibre_point_stored u bound out ho
  have index : Port5Q1_Domain.index u.val=⟨u.val,bound⟩ := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt bound
  rw [index,FoldStoredGeometry.fibre_eq_stored]
  exact ⟨congrArg (fun z => z.re) stored,congrArg (fun z => z.im) stored⟩

theorem line {C : Type} (ops : Port3_NativeGeometryBody.Ops C) (u : Usize)
    (x : U32) (run : (SAQ_Geometry.install ops).op14 u=ok x) :
    S7JoinBasisMachine.decode x=FoldStoredGeometry.sourceX18 (Port5Q1_Domain.index u.val) := by
  have expanded := run
  change R17FibrePointLineNodeActual.line_node
    R17CurrentCM31Semantics.operations R17CurrentM31Semantics.operations u=ok x at expanded
  unfold R17FibrePointLineNodeActual.line_node at expanded
  obtain ⟨p,hp,_⟩ := Port3_PushFrame.bind_success _ _ _ expanded
  have bound := point_bound u p hp
  have stored := R17CurrentDomainSource.successful_line_node_stored u bound x run
  have index : Port5Q1_Domain.index u.val=⟨u.val,bound⟩ := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt bound
  rw [index,FoldStoredGeometry.x18_eq_stored]
  exact stored

#print axioms array_bound
#print axioms point_bound
#print axioms point
#print axioms line
end AspisR1.SAQ_Domain
end
