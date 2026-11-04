import Lean
import NFN_PhaseTransport
import NFN_ReserveOwner
import NFN_GeometryPart07
import NEB_PureFrame

-- BEGIN copied NFB_GeometryComposed: evidence/slice-q-compose5-20261104/NFB_GeometryComposed.lean
set_option autoImplicit false
noncomputable section
namespace NFN_NFB_GeometryComposed
open Aeneas Aeneas.Std Result ControlFlow AspisR1
open NFN_NEW_GeometryRawInterface NFN_NEW_GeometryDictionary NFN_NFB_GatherTrace
open NFN_NFB_PhysicalFrame NFN_NFB_PrivateFrame
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
 NEB_PureFrame.equality state _ _ (NFN_NEW_GeometryComplete.complete queries start finish)

/-- Root-owned native domain only. Every inner call/buffer/size/trace is
DERIVED from this root's accepted Result and the same terminal computation. -/
theorem accepted_physical (queries : Array U32 22#usize) (start finish : Usize)
 (deployed : NFN_NFB_RangeTrace.Deployed start finish) (heap : Heap)
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
 NFN_NEW_GeometryReverse.Trace flat.val prefixes.val flat.val.length resized.val suffix inverse.val
  (NFN_NEW_GeometryReverse.suffixAfter flat.val flat.val.length suffix)
  (NFN_NEW_GeometryReverse.callLog flat.val prefixes.val flat.val.length suffix) ∧
 out.inverses.val=(List.range lines.val.length).map (Port4C_CollectLoop.record inverse) ∧
 NFN_NFB_CollectorTrace.finish (NFN_NFB_CollectorTrace.fill out.inverses.val
  (⟨[],0⟩ : NFN_NFB_CollectorTrace.Guard (Array U32 5#usize)))=⟨out.inverses.val,out.inverses.val.length⟩ ∧
 NFN_NFB_PhysicalFrame.run (NFN_NFB_GatherFrame.actions rows) (NFN_NFB_ReturnedBuffers.initial heap)
  Place.lines.id=some out.line_z.val ∧
 (∀ count,NFN_NFB_PhysicalFrame.run ((NFN_NFB_GatherFrame.actions rows).take count)
  (NFN_NFB_ReturnedBuffers.initial heap) 0=heap 0) ∧
 (∀ count,NFN_NFB_PhysicalFrame.run
  ((NFN_NFB_TerminalFrame.actions flat.val prefixes.val suffix flat.val.length groups.val).take count)
  (NFN_NFB_PhysicalFrame.run (NFN_NFB_GatherFrame.actions rows) (NFN_NFB_ReturnedBuffers.initial heap)) 0=heap 0) := by
 obtain ⟨order,bound,n⟩ := NFN_NFB_RangeTrace.bounds start finish deployed
 obtain ⟨rows,it,lines,flat,prefixes,product,suffix,groups,nrows,hflat,hlines,size,plen,
  hp,hs,hstart,hline,hgroups,ending,last,payload,gatherFrame,terminalFrame⟩ :=
  NFN_NFB_ReturnedBuffers.complete queries start finish deployed heap out accepted
 have lineLength : lines.val.length=rows.length := by rw [hlines,List.length_map]
 have count : lines.val.length≤22 := by rw [lineLength,nrows];omega
 have positive : 0<flat.val.length := by rcases n with h|h <;> omega
 have nonempty : flat.val≠[] := by intro h;rw [h] at positive;cases positive
 obtain ⟨ps,prod,suff,resized,inverse,hp1,len1,hs1,resizeValue,back,inverseLength,trace,contents,publication⟩ :=
  NFN_NFB_TerminalAssociation.complete start it lines flat out ending nonempty count (by omega) last
 have same : (ps,prod)=(prefixes,product) := Result.ok.inj (hp1.symm.trans hp)
 cases same
 have suffixSame : suff=suffix := Result.ok.inj (hs1.symm.trans hs)
 subst suff
 exact ⟨rows,lines,flat,prefixes,product,suffix,resized,inverse,groups,nrows,hflat,hlines,
  hstart,hline,hgroups,hp,plen,hs,resizeValue,back,inverseLength,trace,contents,publication,
  payload,gatherFrame,terminalFrame⟩
#print axioms result_state_effects
#print axioms accepted_physical
end NFN_NFB_GeometryComposed
end
-- END copied NFB_GeometryComposed

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
