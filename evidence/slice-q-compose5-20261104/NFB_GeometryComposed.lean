import NFB_ReturnedBuffers
import NFB_TerminalAssociation
import NEB_PureFrame
set_option autoImplicit false
noncomputable section
namespace NFB_GeometryComposed
open Aeneas Aeneas.Std Result ControlFlow AspisR1
open NEW_GeometryRawInterface NEW_GeometryDictionary NFB_GatherTrace
open NFB_PhysicalFrame NFB_PrivateFrame
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20

/-- Concrete full model G: exact partial Result, persistent state and semantic
effects. Native physical interpretation is a separately checked hybrid packet;
this does not assert empty native panic I/O or verify the compiler. -/
theorem result_state_effects {State Event : Type} (queries : Array U32 22#usize)
 (start finish : Usize) (state : State) :
 NEB_PureFrame.run (Event:=Event) state
  (Port3_QueryInstall.result (resultMap answer
   (NEW_GeometryActual.verifier.QueryGeometry.for_range queries start finish)))=
 NEB_PureFrame.run state (Port3_GeometryStage.geometry adopted queries start finish) :=
 NEB_PureFrame.equality state _ _ (NEW_GeometryComplete.complete queries start finish)

/-- Root-owned native domain only. Every inner call/buffer/size/trace is
DERIVED from this root's accepted Result and the same terminal computation. -/
theorem accepted_physical (queries : Array U32 22#usize) (start finish : Usize)
 (deployed : NFB_RangeTrace.Deployed start finish) (heap : Heap)
 (out : AspisR1Stage2.verifier.QueryGeometry)
 (accepted : resultMap answer
  (NEW_GeometryActual.verifier.QueryGeometry.for_range queries start finish)=ok (.Ok out)) :
 ∃ (rows : List Row) (lines flat prefixes : Vec) (product suffix : U32) (resized inverse : Vec)
   (groups : alloc.vec.Vec (Array U32 5#usize)),
 rows.length=finish.val-start.val ∧ flat.val=rows.flatMap (fun r=>r.words) ∧
 lines.val=rows.map (fun r=>r.lineZ) ∧ out.start=start ∧ out.line_z=lines ∧ out.inverses=groups ∧
 adopted.op13 flat.deref=ok (prefixes,product) ∧ prefixes.val.length=flat.val.length ∧
 adopted.op11 product=ok suffix ∧ resized.val=List.replicate flat.val.length 0#u32 ∧
 NEW_GeometryActual.verifier.QueryGeometry.for_range_loop0_loop0
  (Port4C_Reverse.reverse (alloc.vec.Vec.len flat)) flat prefixes suffix resized=ok inverse ∧
 inverse.val.length=flat.val.length ∧
 NEW_GeometryReverse.Trace flat.val prefixes.val flat.val.length resized.val suffix inverse.val
  (NEW_GeometryReverse.suffixAfter flat.val flat.val.length suffix)
  (NEW_GeometryReverse.callLog flat.val prefixes.val flat.val.length suffix) ∧
 out.inverses.val=(List.range lines.val.length).map (Port4C_CollectLoop.record inverse) ∧
 NFB_CollectorTrace.finish (NFB_CollectorTrace.fill out.inverses.val
  (⟨[],0⟩ : NFB_CollectorTrace.Guard (Array U32 5#usize)))=⟨out.inverses.val,out.inverses.val.length⟩ ∧
 NFB_PhysicalFrame.run (NFB_GatherFrame.actions rows) (NFB_ReturnedBuffers.initial heap)
  Place.lines.id=some out.line_z.val ∧
 (∀ count,NFB_PhysicalFrame.run ((NFB_GatherFrame.actions rows).take count)
  (NFB_ReturnedBuffers.initial heap) 0=heap 0) ∧
 (∀ count,NFB_PhysicalFrame.run
  ((NFB_TerminalFrame.actions flat.val prefixes.val suffix flat.val.length groups.val).take count)
  (NFB_PhysicalFrame.run (NFB_GatherFrame.actions rows) (NFB_ReturnedBuffers.initial heap)) 0=heap 0) := by
 obtain ⟨order,bound,n⟩ := NFB_RangeTrace.bounds start finish deployed
 obtain ⟨rows,it,lines,flat,prefixes,product,suffix,groups,nrows,hflat,hlines,size,plen,
  hp,hs,hstart,hline,hgroups,ending,last,payload,gatherFrame,terminalFrame⟩ :=
  NFB_ReturnedBuffers.complete queries start finish deployed heap out accepted
 have lineLength : lines.val.length=rows.length := by rw [hlines,List.length_map]
 have count : lines.val.length≤22 := by rw [lineLength,nrows];omega
 have positive : 0<flat.val.length := by rcases n with h|h <;> omega
 have nonempty : flat.val≠[] := by intro h;rw [h] at positive;cases positive
 obtain ⟨ps,prod,suff,resized,inverse,hp1,len1,hs1,resizeValue,back,inverseLength,trace,contents,publication⟩ :=
  NFB_TerminalAssociation.complete start it lines flat out ending nonempty count (by omega) last
 have same : (ps,prod)=(prefixes,product) := Result.ok.inj (hp1.symm.trans hp)
 cases same
 have suffixSame : suff=suffix := Result.ok.inj (hs1.symm.trans hs)
 subst suff
 exact ⟨rows,lines,flat,prefixes,product,suffix,resized,inverse,groups,nrows,hflat,hlines,
  hstart,hline,hgroups,hp,plen,hs,resizeValue,back,inverseLength,trace,contents,publication,
  payload,gatherFrame,terminalFrame⟩
#print axioms result_state_effects
#print axioms accepted_physical
end NFB_GeometryComposed
end
