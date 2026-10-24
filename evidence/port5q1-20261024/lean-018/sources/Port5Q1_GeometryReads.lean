import Port5Q1_ListCells
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port5Q1_GeometryReads
open Aeneas Aeneas.Std Result AspisR1Stage2
open Port3_NativeGeometryBody
abbrev FP := ZMod AspisCircleGroupOrder.P

def queryAt (queries : Array U32 22#usize) (i : Nat) : U32 := queries.val[i]?.getD 0#u32
def lane (a : Array U32 5#usize) (j : Fin 5) : U32 := a.val[j.val]?.getD 0#u32

def forQuery (geometry : verifier.QueryGeometry) (i : Usize) : Result (Array U32 5#usize) :=
  alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (Array U32 5#usize))
    geometry.inverses (Usize.wrapping_sub i geometry.start)

structure Binding (queries : Array U32 22#usize) (start end1 : Usize)
    (geometry : verifier.QueryGeometry) : Prop where
  start_eq : geometry.start=start
  order : start.val<end1.val
  bound : end1.val≤22
  line_size : geometry.line_z.val.length=end1.val-start.val
  inverse_size : geometry.inverses.val.length=end1.val-start.val
  line : ∀ i, i<end1.val-start.val →
    S7JoinBasisMachine.decode (geometry.line_z.val[i]?.getD 0#u32)=
      Port5Q1_Domain.lineZ (queryAt queries (start.val+i)).val
  inverses : ∀ i, i<end1.val-start.val → ∀ j : Fin 5,
    S7JoinBasisMachine.decode (lane (geometry.inverses.val[i]?.getD
      (Array.make 5#usize [0#u32,0#u32,0#u32,0#u32,0#u32])) j)=
      ((Port5Q1_Domain.words (queryAt queries (start.val+i)).val)[j.val]?.getD 0)⁻¹

variable {CoreError : Type}
theorem accepted (ops : Ops CoreError)
    (leaves : Port5Q1_GeometryCanonical.SessionAPrimitives ops)
    (domain : Port5Q1_Domain.SessionADomain ops)
    (multiply : ops.op9=AspisR1Qm31ArithmeticProbe.field.M31.mul)
    (one : ops.op7=ok (1#u32))
    (inverseLeaf : ops.op11=Port4C_InverseExecution.inverse_owned)
    (queries : Array U32 22#usize) (start end1 : Usize) (out : verifier.QueryGeometry)
    (nonempty : start.val<end1.val)
    (run : Port3_GeometryStage.geometry (Port5Q1_GeometryTerminal.install ops)
      queries start end1=ok (.Ok out)) : Binding queries start end1 out := by
  obtain ⟨flat,inverse,hs,hlen,flatlen,canon,nonzero,invlen,values,groups,flatMeaning,lineMeaning⟩ :=
    Port5Q1_GeometryModel.for_range ops leaves domain multiply one inverseLeaf queries start end1 out nonempty run
  have range := Port4C_GeometryRange.accepted_range (Port5Q1_GeometryTerminal.install ops)
    queries start end1 out run
  obtain ⟨_,order,bound,_,_⟩ := range
  let selected := (queries.val.drop start.val).take (end1.val-start.val)
  have selectedLen : selected.length=end1.val-start.val := by
    dsimp [selected]
    rw [List.length_take,List.length_drop,queries.property]
    change min (end1.val-start.val) (22-start.val)=_
    omega
  have selectedAt : ∀ i, i<end1.val-start.val → selected[i]?.getD 0#u32=queryAt queries (start.val+i) := by
    intro i hi
    simp only [selected,List.getElem?_take,List.getElem?_drop,queryAt]
    rw [if_pos hi]
  refine ⟨hs,nonempty,bound,hlen,?_,?_,?_⟩
  · rw [groups,List.length_map,List.length_range]
  · intro i hi
    have eq := congrArg (fun xs : List FP => xs[i]?.getD 0) lineMeaning
    rw [Port5Q1_ListCells.map_cell] at eq
    change S7JoinBasisMachine.decode (out.line_z.val[i]?.getD 0#u32)=
      (selected.map (fun q => Port5Q1_Domain.lineZ q.val))[i]?.getD 0 at eq
    rw [List.getElem?_map] at eq
    have get : selected[i]?=some (queryAt queries (start.val+i)) := by
      rw [List.getElem?_eq_getElem (by rw [selectedLen]; exact hi)]
      have := selectedAt i hi
      simpa only [List.getElem?_eq_getElem (by rw [selectedLen]; exact hi),Option.getD_some] using congrArg some this
    rw [get] at eq
    exact eq
  · intro i hi j
    have groupRead : out.inverses.val[i]?=some (Port4C_CollectLoop.record inverse i) := by
      rw [groups,List.getElem?_map,List.getElem?_range (by exact hi)]
      rfl
    rw [groupRead,Option.getD_some,lane,Port5Q1_ListCells.record_cell,values (5*i+j.val) (by omega)]
    congr 1
    have eq := congrArg (fun xs : List FP => xs[5*i+j.val]?.getD 0) flatMeaning
    rw [Port5Q1_ListCells.map_cell] at eq
    change S7JoinBasisMachine.decode (Port4C_BatchInverse.cell flat.val (5*i+j.val))=
      (selected.flatMap (fun q => Port5Q1_Domain.words q.val))[5*i+j.val]?.getD 0 at eq
    rw [Port5Q1_ListCells.flat_cell _ (by intro x; rfl) selected i j.val
      (by rw [selectedLen]; exact hi) j.isLt] at eq
    have same : selected[i]=queryAt queries (start.val+i) := by
      simpa only [List.getElem?_eq_getElem (by rw [selectedLen]; exact hi),Option.getD_some] using selectedAt i hi
    rw [same] at eq
    exact eq

#print axioms accepted
end AspisR1.Port5Q1_GeometryReads
end
