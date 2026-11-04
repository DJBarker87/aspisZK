import Lean
import NFN_PhaseTransport
import NFN_ReserveOwner
import NFN_GeometryPart06
import NFN_GeometryPart04

-- BEGIN copied NFB_TerminalFrame: evidence/slice-q-compose5-20261104/NFB_TerminalFrame.lean
set_option autoImplicit false
namespace NFN_NFB_TerminalFrame
open Aeneas.Std AspisR1 NFN_NFB_PhysicalFrame NFN_NFB_PrivateFrame

def resize : Nat → List Action
 | 0 => []
 | n+1 => append .inverse [0#u32] :: resize n

def collect : List (Array U32 5#usize) → List Action
 | [] => []
 | row::rs => append .rows row.val :: collect rs

def actions (flat prefixes : List U32) (suffix : U32) (count : Nat)
 (groups : List (Array U32 5#usize)) : List Action :=
 [allocate .prefixes prefixes,allocate .inverse []]++resize count++
 NFN_NFB_ReverseTrace.writes flat prefixes count suffix++
 [allocate .rows []]++collect groups++
 [release .inverse,release .prefixes,release .flat]

theorem resize_owned (n : Nat) : ∀ a∈resize n,Private a := by
 induction n with
 | zero => simp [resize]
 | succ n ih =>
  intro a ha
  simp only [resize,List.mem_cons] at ha
  rcases ha with rfl | ha
  · exact Private.append _ _
  · exact ih a ha

theorem collect_owned (groups : List (Array U32 5#usize)) : ∀ a∈collect groups,Private a := by
 induction groups with
 | nil => simp [collect]
 | cons row rs ih =>
  intro a ha
  simp only [collect,List.mem_cons] at ha
  rcases ha with rfl | ha
  · exact Private.append _ _
  · exact ih a ha

theorem owned (flat prefixes : List U32) (suffix : U32) (count : Nat)
 (groups : List (Array U32 5#usize)) :
 ∀ a∈actions flat prefixes suffix count groups,Private a := by
 intro a ha
 simp only [actions,List.mem_append] at ha
 rcases ha with ((((h0 | hr) | hw) | hrow) | hc) | hrel
 · simp only [List.mem_cons,List.not_mem_nil,or_false] at h0
   rcases h0 with rfl | rfl <;> exact Private.allocate _ _
 · exact resize_owned count a hr
 · exact NFN_NFB_ReverseTrace.owned flat prefixes count suffix a hw
 · simp only [List.mem_singleton] at hrow
   subst a
   exact Private.allocate _ _
 · exact collect_owned groups a hc
 · simp only [List.mem_cons,List.not_mem_nil,or_false] at hrel
   rcases hrel with rfl | rfl | rfl <;> exact Private.release _

theorem query_frame (flat prefixes : List U32) (suffix : U32) (count : Nat)
 (groups : List (Array U32 5#usize)) (heap : Heap) (countTaken : Nat) :
 NFN_NFB_PhysicalFrame.run ((actions flat prefixes suffix count groups).take countTaken) heap 0=heap 0 :=
 protected_query _ heap countTaken (owned flat prefixes suffix count groups)
#print axioms resize_owned
#print axioms collect_owned
#print axioms owned
#print axioms query_frame
end NFN_NFB_TerminalFrame
-- END copied NFB_TerminalFrame
-- BEGIN copied NFB_PrefixDomain: evidence/slice-q-compose5-20261104/NFB_PrefixDomain.lean
set_option autoImplicit false
noncomputable section
namespace NFN_NFB_PrefixDomain
open Aeneas Aeneas.Std Result AspisR1
open NFN_NEW_GeometryDictionary

theorem model_length (flat prefixes : List U32) (product : U32) :
 (S7Kani2PrefixLoop.model flat prefixes product).1.length=prefixes.length+flat.length := by
 induction flat generalizing prefixes product with
 | nil => simp [S7Kani2PrefixLoop.model]
 | cons x xs ih =>
  rw [S7Kani2PrefixLoop.model,ih]
  simp only [List.length_append,List.length_singleton,List.length_cons,List.length_nil]
  omega

theorem complete (flat : alloc.vec.Vec U32) (bound : flat.val.length≤110) :
 ∃ (prefixes : alloc.vec.Vec U32) (product : U32),
 adopted.op13 flat.deref=ok (prefixes,product) ∧ prefixes.val.length=flat.val.length := by
 obtain ⟨prefixes,product,run,meaning⟩ := Port4C_PrefixMeaning.total
  NFN_NEW_GeometryPrefix.leaves rfl rfl flat.deref bound
 refine ⟨prefixes,product,?_,?_⟩
 · exact run
 · have values:=congrArg (fun p : List U32 × U32=>p.1.length) meaning
   rw [model_length] at values
   simpa only [alloc.vec.Vec.deref,List.length_nil,Nat.zero_add] using values
#print axioms model_length
#print axioms complete
end NFN_NFB_PrefixDomain
end
-- END copied NFB_PrefixDomain
-- BEGIN copied NFB_ReturnedBuffers: evidence/slice-q-compose5-20261104/NFB_ReturnedBuffers.lean
set_option autoImplicit false
noncomputable section
namespace NFN_NFB_ReturnedBuffers
open Aeneas Aeneas.Std Result ControlFlow AspisR1
open NFN_NEW_GeometryRawInterface NFN_NEW_GeometryDictionary NFN_NFB_GatherTrace
open NFN_NFB_PhysicalFrame NFN_NFB_PrivateFrame
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20

def initial (heap : Heap) : Heap :=
 NFN_NFB_PhysicalFrame.run [allocate .lines [],allocate .flat []] heap

theorem initial_frame (heap : Heap) :
 initial heap 0=heap 0 ∧ initial heap Place.flat.id=some [] ∧
 initial heap Place.lines.id=some [] := by
 simp [initial,NFN_NFB_PhysicalFrame.run,allocate,Action.apply,write,Place.id]

/-- The actual successful root fixes the SAME gather, terminal, and returned
line allocation. Its physical query frame is composed without a trace premise. -/
theorem complete (queries : Array U32 22#usize) (start finish : Usize)
 (deployed : NFN_NFB_RangeTrace.Deployed start finish) (heap : Heap)
 (out : AspisR1Stage2.verifier.QueryGeometry)
 (accepted : resultMap answer
  (NEW_GeometryActual.verifier.QueryGeometry.for_range queries start finish)=ok (.Ok out)) :
 ∃ (rows : List Row) (terminal : It) (lines flat prefixes : Vec)
   (product suffix : U32) (groups : alloc.vec.Vec (Array U32 5#usize)),
 rows.length=finish.val-start.val ∧
 flat.val=rows.flatMap (fun r=>r.words) ∧ lines.val=rows.map (fun r=>r.lineZ) ∧
 flat.val.length=5*rows.length ∧ prefixes.val.length=flat.val.length ∧
 adopted.op13 flat.deref=ok (prefixes,product) ∧ adopted.op11 product=ok suffix ∧
 out.start=start ∧ out.line_z=lines ∧ out.inverses=groups ∧
 terminal.i=terminal.slice.val.length ∧
 Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0.body adopted start terminal lines flat=ok (done (.Ok out)) ∧
 NFN_NFB_PhysicalFrame.run (NFN_NFB_GatherFrame.actions rows) (initial heap) Place.lines.id=some out.line_z.val ∧
 (∀ count,NFN_NFB_PhysicalFrame.run ((NFN_NFB_GatherFrame.actions rows).take count) (initial heap) 0=heap 0) ∧
 (∀ count,NFN_NFB_PhysicalFrame.run
  ((NFN_NFB_TerminalFrame.actions flat.val prefixes.val suffix flat.val.length groups.val).take count)
  (NFN_NFB_PhysicalFrame.run (NFN_NFB_GatherFrame.actions rows) (initial heap)) 0=heap 0) := by
 obtain ⟨order,bound,count⟩ := NFN_NFB_RangeTrace.bounds start finish deployed
 obtain ⟨rows,terminal,lines,flat,nrows,hflat,hlines,size,lineSize,ending,last⟩ :=
  NFN_NFB_AcceptedGather.complete queries start finish order bound out accepted
 have positive : 0<flat.val.length := by rcases count with c|c <;> omega
 have nonempty : flat.val≠[] := by intro h;rw [h] at positive;cases positive
 obtain ⟨prefixes,product,suffix,zero,resized,inverse,rev,mapped,groups,
  hp,hs,hz,hr,hrev,hback,hmap,hcollect,startField,lineField,groupsField⟩ :=
  NFN_NFB_TerminalCuts.complete start terminal lines flat out ending nonempty last
 obtain ⟨ps,prod,prefixRun,prefixLength⟩ := NFN_NFB_PrefixDomain.complete flat (by omega)
 have same : (ps,prod)=(prefixes,product) := Result.ok.inj (prefixRun.symm.trans hp)
 cases same
 obtain ⟨initialQuery,initialFlat,initialLines⟩ := initial_frame heap
 obtain ⟨flatPayload,linePayload⟩ := NFN_NFB_GatherFrame.payloads rows (initial heap) [] [] initialFlat initialLines
 have frame := fun count=>NFN_NFB_GatherFrame.query_frame rows (initial heap) count
 refine ⟨rows,terminal,lines,flat,prefixes,product,suffix,groups,nrows,hflat,hlines,?_,prefixLength,
  hp,hs,startField,lineField,groupsField,ending,last,?_,?_,?_⟩
 · omega
 · rw [lineField,hlines]
   simpa only [List.nil_append] using linePayload
 · intro count
   exact (frame count).trans initialQuery
 · intro count
   rw [NFN_NFB_TerminalFrame.query_frame]
   exact (NFN_NFB_PhysicalFrame.trace_frame _ (initial heap) 0
    (fun a ha=>NFN_NFB_PrivateFrame.disjoint a (NFN_NFB_GatherFrame.owned rows a ha))).trans initialQuery
#print axioms initial_frame
#print axioms complete
end NFN_NFB_ReturnedBuffers
end
-- END copied NFB_ReturnedBuffers
-- BEGIN copied NFB_ReverseAssociation: evidence/slice-q-compose5-20261104/NFB_ReverseAssociation.lean
set_option autoImplicit false
noncomputable section
namespace NFN_NFB_ReverseAssociation
open Aeneas Aeneas.Std Result AspisR1
open NFN_NEW_GeometryRawInterface NFN_NFB_PhysicalFrame NFN_NFB_PrivateFrame

theorem complete (flat prefixes inverse : alloc.vec.Vec U32) (suffix : U32) (index : Usize)
 (bound : index.val≤110) (hf : index.val≤flat.val.length)
 (hp : index.val≤prefixes.val.length) (hi : index.val ≤ inverse.val.length)
 (heap : Heap) (selected : heap Place.inverse.id=some inverse.val) :
 ∃ out : alloc.vec.Vec U32,
 NEW_GeometryActual.verifier.QueryGeometry.for_range_loop0_loop0
  (Port4C_Reverse.reverse index) flat prefixes suffix inverse=ok out ∧
 NFN_NEW_GeometryReverse.Trace flat.val prefixes.val index.val inverse.val suffix out.val
  (NFN_NEW_GeometryReverse.suffixAfter flat.val index.val suffix)
  (NFN_NEW_GeometryReverse.callLog flat.val prefixes.val index.val suffix) ∧
 NFN_NFB_PhysicalFrame.run (NFN_NFB_ReverseTrace.writes flat.val prefixes.val index.val suffix)
  heap Place.inverse.id=some out.val ∧
 (∀ count,NFN_NFB_PhysicalFrame.run
  ((NFN_NFB_ReverseTrace.writes flat.val prefixes.val index.val suffix).take count) heap 0=heap 0) := by
 obtain ⟨out,owned,meaning,length⟩ := Port4C_OwnedInverse.inverse_refines
  flat prefixes inverse suffix index bound hf hp hi
 have multiply : ops.op9=AspisR1Qm31ArithmeticProbe.field.M31.mul := by
  funext x y
  exact NFN_NEW_GeometryArithmetic.multiply_probe x y
 have native := Port4C_InverseLoop.from_owned ops multiply flat prefixes inverse out suffix index bound owned
 have trace := NFN_NFB_ReverseTrace.complete flat.val prefixes.val inverse.val index.val suffix hi
 have physical := NFN_NFB_ReverseTrace.payload flat.val prefixes.val inverse.val index.val suffix heap selected
 refine ⟨out,?_,?_,?_,?_⟩
 · rw [NFN_NEW_GeometryRawHelpers.backward]
   exact native
 · rw [meaning]
   exact trace
 · rw [meaning]
   exact physical
 · exact fun count=>protected_query _ heap count (NFN_NFB_ReverseTrace.owned _ _ _ _)
#print axioms complete
end NFN_NFB_ReverseAssociation
end
-- END copied NFB_ReverseAssociation
-- BEGIN copied NFB_BackwardCongr: evidence/slice-q-compose5-20261104/NFB_BackwardCongr.lean
set_option autoImplicit false
noncomputable section
namespace NFN_NFB_BackwardCongr
open Aeneas Aeneas.Std AspisR1
open NFN_NEW_GeometryRawInterface NFN_NEW_GeometryDictionary

theorem body {CE : Type} (a b : Port3_NativeGeometryBody.Ops CE)
 (multiply : a.op9=b.op9) (flat prefixes : alloc.vec.Vec U32)
 (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
 (suffix : U32) (inverse : alloc.vec.Vec U32) :
 Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0_loop0.body a flat prefixes iter suffix inverse=
 Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0_loop0.body b flat prefixes iter suffix inverse := by
 simp only [Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0_loop0.body,multiply]

theorem loop {CE : Type} (a b : Port3_NativeGeometryBody.Ops CE)
 (multiply : a.op9=b.op9) (flat prefixes : alloc.vec.Vec U32)
 (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
 (suffix : U32) (inverse : alloc.vec.Vec U32) :
 Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0_loop0 a iter flat prefixes suffix inverse=
 Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0_loop0 b iter flat prefixes suffix inverse := by
 unfold Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0_loop0
 simp only [body a b multiply]

theorem multiply : ops.op9=adopted.op9 := by
 change NEW_GeometryActual.aspis_core.field.M31.mul=AspisR1Qm31ArithmeticProbe.field.M31.mul
 exact funext (fun x=>funext (NFN_NEW_GeometryArithmetic.multiply_probe x))
#print axioms body
#print axioms loop
#print axioms multiply
end NFN_NFB_BackwardCongr
end
-- END copied NFB_BackwardCongr
-- BEGIN copied NFB_BackwardTransport: evidence/slice-q-compose5-20261104/NFB_BackwardTransport.lean
set_option autoImplicit false
noncomputable section
namespace NFN_NFB_BackwardTransport
open Aeneas Aeneas.Std AspisR1
open NFN_NEW_GeometryRawInterface NFN_NEW_GeometryDictionary

theorem body (flat prefixes : alloc.vec.Vec U32)
 (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
 (suffix : U32) (inverse : alloc.vec.Vec U32) :
 Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0_loop0.body ops flat prefixes iter suffix inverse=
 Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0_loop0.body adopted flat prefixes iter suffix inverse := by
 exact NFN_NFB_BackwardCongr.body ops adopted NFN_NFB_BackwardCongr.multiply flat prefixes iter suffix inverse

theorem complete (flat prefixes : alloc.vec.Vec U32)
 (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
 (suffix : U32) (inverse : alloc.vec.Vec U32) :
 NEW_GeometryActual.verifier.QueryGeometry.for_range_loop0_loop0 iter flat prefixes suffix inverse=
 Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0_loop0 adopted iter flat prefixes suffix inverse := by
 rw [NFN_NEW_GeometryRawHelpers.backward]
 exact NFN_NFB_BackwardCongr.loop ops adopted NFN_NFB_BackwardCongr.multiply flat prefixes iter suffix inverse
#print axioms body
#print axioms complete
end NFN_NFB_BackwardTransport
end
-- END copied NFB_BackwardTransport
-- BEGIN copied NFB_ResizeAssociation: evidence/slice-q-compose5-20261104/NFB_ResizeAssociation.lean
set_option autoImplicit false
namespace NFN_NFB_ResizeAssociation
open Aeneas Aeneas.Std Result NFN_NFB_PhysicalFrame NFN_NFB_PrivateFrame

theorem complete (count : Usize) :
 ∃ out : alloc.vec.Vec U32,
 alloc.vec.Vec.resize core.marker.CopyU32.cloneInst
  (alloc.vec.Vec.with_capacity U32 count) count 0#u32=ok out ∧
 out.val=List.replicate count.val 0#u32 := by
 obtain ⟨out,run,values⟩ := WP.spec_imp_exists
  (alloc.vec.Vec.resize_spec core.marker.CopyU32.cloneInst
   (alloc.vec.Vec.with_capacity U32 count) count 0#u32 rfl)
 refine ⟨out,run,?_⟩
 simpa [alloc.vec.Vec.with_capacity,List.resize] using values

theorem payload (count : Nat) (heap : Heap)
 (selected : heap Place.inverse.id=some []) :
 NFN_NFB_PhysicalFrame.run (NFN_NFB_TerminalFrame.resize count) heap Place.inverse.id=
 some (List.replicate count 0#u32) := by
 have general : ∀ (n : Nat) (before : List U32) (heap : Heap),
    heap Place.inverse.id=some before →
    NFN_NFB_PhysicalFrame.run (NFN_NFB_TerminalFrame.resize n) heap Place.inverse.id=
    some (before++List.replicate n 0#u32) := by
  intro n
  induction n with
  | zero => intro before heap h;simpa only [NFN_NFB_TerminalFrame.resize,NFN_NFB_PhysicalFrame.run,List.replicate_zero,List.append_nil] using h
  | succ n ih =>
   intro before heap h
   change NFN_NFB_PhysicalFrame.run (NFN_NFB_TerminalFrame.resize n)
    ((append .inverse [0#u32]).apply heap) Place.inverse.id=_
   have next : (append .inverse [0#u32]).apply heap Place.inverse.id=some (before++[0#u32]) := by
    simp only [append,Action.apply,write,ite_true,h,Option.map_some]
   have result:=ih (before++[0#u32]) _ next
   simpa only [List.append_assoc,List.replicate_succ,List.singleton_append] using result
 simpa only [List.nil_append] using general count [] heap selected
#print axioms complete
#print axioms payload
end NFN_NFB_ResizeAssociation
-- END copied NFB_ResizeAssociation
-- BEGIN copied NFB_TerminalAssociation: evidence/slice-q-compose5-20261104/NFB_TerminalAssociation.lean
set_option autoImplicit false
noncomputable section
namespace NFN_NFB_TerminalAssociation
open Aeneas Aeneas.Std Result ControlFlow AspisR1
open NFN_NEW_GeometryDictionary NFN_NFB_GatherTrace
open NFN_NFB_PhysicalFrame NFN_NFB_PrivateFrame

/-- SAME terminal buffers and actual child Results instantiate every native
reverse/collect domain. Child success is derived from this accepted terminal. -/
theorem complete (start : Usize) (it : It) (lines flat : Vec)
 (out : AspisR1Stage2.verifier.QueryGeometry)
 (ending : it.i=it.slice.val.length) (nonempty : flat.val≠[])
 (count : lines.val.length≤22) (size : flat.val.length=5*lines.val.length)
 (accepted : Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0.body adopted
  start it lines flat=ok (done (.Ok out))) :
 ∃ (prefixes : Vec) (product suffix : U32) (resized inverse : Vec),
 adopted.op13 flat.deref=ok (prefixes,product) ∧ prefixes.val.length=flat.val.length ∧
 adopted.op11 product=ok suffix ∧ resized.val=List.replicate flat.val.length 0#u32 ∧
 NEW_GeometryActual.verifier.QueryGeometry.for_range_loop0_loop0
  (Port4C_Reverse.reverse (alloc.vec.Vec.len flat)) flat prefixes suffix resized=ok inverse ∧
 inverse.val.length=flat.val.length ∧
 NFN_NEW_GeometryReverse.Trace flat.val prefixes.val flat.val.length resized.val suffix inverse.val
  (NFN_NEW_GeometryReverse.suffixAfter flat.val flat.val.length suffix)
  (NFN_NEW_GeometryReverse.callLog flat.val prefixes.val flat.val.length suffix) ∧
 out.inverses.val=(List.range lines.val.length).map (Port4C_CollectLoop.record inverse) ∧
 NFN_NFB_CollectorTrace.finish
  (NFN_NFB_CollectorTrace.fill out.inverses.val (⟨[],0⟩ : NFN_NFB_CollectorTrace.Guard (Array U32 5#usize)))=
  ⟨out.inverses.val,out.inverses.val.length⟩ := by
 obtain ⟨prefixes,product,suffix,zero,resized,inverse,rev,mapped,groups,
  hp,hs,hz,hr,hrev,hback,hmap,hcollect,startField,lineField,groupsField⟩ :=
  NFN_NFB_TerminalCuts.complete start it lines flat out ending nonempty accepted
 obtain ⟨ps,prod,prefixRun,prefixLen⟩ := NFN_NFB_PrefixDomain.complete flat (by omega)
 have same : (ps,prod)=(prefixes,product) := Result.ok.inj (prefixRun.symm.trans hp)
 cases same
 have zeroValue : zero=0#u32 := (Result.ok.inj hz).symm
 subst zero
 obtain ⟨rs,resizeRun,resizeValue⟩ := NFN_NFB_ResizeAssociation.complete (alloc.vec.Vec.len flat)
 have sameResize : rs=resized := Result.ok.inj (resizeRun.symm.trans hr)
 subst rs
 have resizeLength : resized.val.length=flat.val.length := by
  rw [resizeValue,List.length_replicate]
  rfl
 have revValue : rev=Port4C_Reverse.reverse (alloc.vec.Vec.len flat) := (Result.ok.inj hrev).symm
 subst rev
 have native : NEW_GeometryActual.verifier.QueryGeometry.for_range_loop0_loop0
  (Port4C_Reverse.reverse (alloc.vec.Vec.len flat)) flat prefixes suffix resized=ok inverse := by
  rw [NFN_NFB_BackwardTransport.complete]
  exact hback
 let heap : Heap := fun p=>if p=Place.inverse.id then some resized.val else none
 obtain ⟨other,otherRun,trace,physical,frame⟩ := NFN_NFB_ReverseAssociation.complete flat prefixes resized suffix
  (alloc.vec.Vec.len flat) (by change flat.val.length≤110;omega)
  (by rfl) (by change flat.val.length≤prefixes.val.length;omega)
  (by change flat.val.length ≤ resized.val.length;omega) heap (by simp [heap])
 have sameInverse : other=inverse := Result.ok.inj (otherRun.symm.trans native)
 subst other
 have inverseLength : inverse.val.length=flat.val.length := by
  have t:=NFN_NEW_GeometryReverse.state flat.val prefixes.val trace
  rw [t.1]
  have preserve : ∀ (n : Nat) (xs : List U32) (s : U32),
      (Port4C_OwnedInverse.model flat.val prefixes.val n xs s).length=xs.length := by
   intro n
   induction n with
   | zero => intros;rfl
   | succ n ih => intro xs s;rw [Port4C_OwnedInverse.model,ih,List.length_set]
  rw [preserve,resizeLength]
 obtain ⟨collected,collectRun,contents,length⟩ := Port4C_CollectLoop.total
  (Port4C_GeometryInverse.install
   (NFN_NEB_ActualGeometryModel.install NFN_NEW_GeometryRawInterface.ops NFN_NEW_GeometryDictionary.err))
  inverse (alloc.vec.Vec.len lines) count (by simpa only [alloc.vec.Vec.len_val] using inverseLength.trans size)
 have mappedValue : mapped=⟨{start:=0#usize,«end»:=alloc.vec.Vec.len lines},inverse⟩ := (Result.ok.inj hmap).symm
 subst mapped
 have sameGroups : collected=groups := Result.ok.inj (collectRun.symm.trans hcollect)
 subst collected
 refine ⟨prefixes,product,suffix,resized,inverse,hp,prefixLen,hs,resizeValue,native,inverseLength,trace,?_,?_⟩
 · rw [groupsField]
   exact contents
 · exact NFN_NFB_CollectorTrace.complete out.inverses.val
#print axioms complete
end NFN_NFB_TerminalAssociation
end
-- END copied NFB_TerminalAssociation

run_cmd do
 let env ← Lean.getEnv
 for (name, info) in env.constants do
  if info.isTheorem && (env.getModuleIdxFor? name).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent name)))
