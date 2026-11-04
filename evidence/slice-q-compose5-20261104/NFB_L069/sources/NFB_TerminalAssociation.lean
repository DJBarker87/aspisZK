import NFB_BackwardTransport
import NFB_ResizeAssociation
import NFB_PrefixDomain
set_option autoImplicit false
noncomputable section
namespace NFB_TerminalAssociation
open Aeneas Aeneas.Std Result ControlFlow AspisR1
open NEW_GeometryDictionary NFB_GatherTrace
open NFB_PhysicalFrame NFB_PrivateFrame

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
 NEW_GeometryReverse.Trace flat.val prefixes.val flat.val.length resized.val suffix inverse.val
  (NEW_GeometryReverse.suffixAfter flat.val flat.val.length suffix)
  (NEW_GeometryReverse.callLog flat.val prefixes.val flat.val.length suffix) ∧
 out.inverses.val=(List.range lines.val.length).map (Port4C_CollectLoop.record inverse) ∧
 NFB_CollectorTrace.finish
  (NFB_CollectorTrace.fill out.inverses.val (⟨[],0⟩ : NFB_CollectorTrace.Guard (Array U32 5#usize)))=
  ⟨out.inverses.val,out.inverses.val.length⟩ := by
 obtain ⟨prefixes,product,suffix,zero,resized,inverse,rev,mapped,groups,
  hp,hs,hz,hr,hrev,hback,hmap,hcollect,startField,lineField,groupsField⟩ :=
  NFB_TerminalCuts.complete start it lines flat out ending nonempty accepted
 obtain ⟨ps,prod,prefixRun,prefixLen⟩ := NFB_PrefixDomain.complete flat (by omega)
 have same : (ps,prod)=(prefixes,product) := Result.ok.inj (prefixRun.symm.trans hp)
 cases same
 have zeroValue : zero=0#u32 := (Result.ok.inj hz).symm
 subst zero
 obtain ⟨rs,resizeRun,resizeValue⟩ := NFB_ResizeAssociation.complete (alloc.vec.Vec.len flat)
 have sameResize : rs=resized := Result.ok.inj (resizeRun.symm.trans hr)
 subst rs
 have resizeLength : resized.val.length=flat.val.length := by
  rw [resizeValue,List.length_replicate]
  rfl
 have revValue : rev=Port4C_Reverse.reverse (alloc.vec.Vec.len flat) := (Result.ok.inj hrev).symm
 subst rev
 have native : NEW_GeometryActual.verifier.QueryGeometry.for_range_loop0_loop0
  (Port4C_Reverse.reverse (alloc.vec.Vec.len flat)) flat prefixes suffix resized=ok inverse := by
  rw [NFB_BackwardTransport.complete]
  exact hback
 let heap : Heap := fun p=>if p=Place.inverse.id then some resized.val else none
 obtain ⟨other,otherRun,trace,physical,frame⟩ := NFB_ReverseAssociation.complete flat prefixes resized suffix
  (alloc.vec.Vec.len flat) (by change flat.val.length≤110;omega)
  (by rfl) (by change flat.val.length≤prefixes.val.length;omega)
  (by change flat.val.length ≤ resized.val.length;omega) heap (by simp [heap])
 have sameInverse : other=inverse := Result.ok.inj (otherRun.symm.trans native)
 subst other
 have inverseLength : inverse.val.length=flat.val.length := by
  have t:=NEW_GeometryReverse.state flat.val prefixes.val trace
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
   (NEB_ActualGeometryModel.install NEW_GeometryRawInterface.ops NEW_GeometryDictionary.err))
  inverse (alloc.vec.Vec.len lines) count (by simpa only [alloc.vec.Vec.len_val] using inverseLength.trans size)
 have mappedValue : mapped=⟨{start:=0#usize,«end»:=alloc.vec.Vec.len lines},inverse⟩ := (Result.ok.inj hmap).symm
 subst mapped
 have sameGroups : collected=groups := Result.ok.inj (collectRun.symm.trans hcollect)
 subst collected
 refine ⟨prefixes,product,suffix,resized,inverse,hp,prefixLen,hs,resizeValue,native,inverseLength,trace,?_,?_⟩
 · rw [groupsField]
   exact contents
 · exact NFB_CollectorTrace.complete out.inverses.val
#print axioms complete
end NFB_TerminalAssociation
end
