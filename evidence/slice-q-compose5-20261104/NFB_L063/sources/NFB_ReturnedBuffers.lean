import NFB_AcceptedGather
import NFB_TerminalCuts
import NFB_TerminalFrame
import NFB_PrefixDomain
set_option autoImplicit false
noncomputable section
namespace NFB_ReturnedBuffers
open Aeneas Aeneas.Std Result ControlFlow AspisR1
open NEW_GeometryRawInterface NEW_GeometryDictionary NFB_GatherTrace
open NFB_PhysicalFrame NFB_PrivateFrame
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20

def initial (heap : Heap) : Heap :=
 NFB_PhysicalFrame.run [allocate .lines [],allocate .flat []] heap

theorem initial_frame (heap : Heap) :
 initial heap 0=heap 0 ∧ initial heap Place.flat.id=some [] ∧
 initial heap Place.lines.id=some [] := by
 simp [initial,NFB_PhysicalFrame.run,allocate,Action.apply,write,Place.id]

/-- The actual successful root fixes the SAME gather, terminal, and returned
line allocation. Its physical query frame is composed without a trace premise. -/
theorem complete (queries : Array U32 22#usize) (start finish : Usize)
 (deployed : NFB_RangeTrace.Deployed start finish) (heap : Heap)
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
 NFB_PhysicalFrame.run (NFB_GatherFrame.actions rows) (initial heap) Place.lines.id=some out.line_z.val ∧
 (∀ count,NFB_PhysicalFrame.run ((NFB_GatherFrame.actions rows).take count) (initial heap) 0=heap 0) ∧
 (∀ count,NFB_PhysicalFrame.run
  ((NFB_TerminalFrame.actions flat.val prefixes.val suffix flat.val.length groups.val).take count)
  (NFB_PhysicalFrame.run (NFB_GatherFrame.actions rows) (initial heap)) 0=heap 0) := by
 obtain ⟨order,bound,count⟩ := NFB_RangeTrace.bounds start finish deployed
 obtain ⟨rows,terminal,lines,flat,nrows,hflat,hlines,size,lineSize,ending,last⟩ :=
  NFB_AcceptedGather.complete queries start finish order bound out accepted
 have positive : 0<flat.val.length := by rcases count with c|c <;> omega
 have nonempty : flat.val≠[] := by intro h;rw [h] at positive;cases positive
 obtain ⟨prefixes,product,suffix,zero,resized,inverse,rev,mapped,groups,
  hp,hs,hz,hr,hrev,hback,hmap,hcollect,startField,lineField,groupsField⟩ :=
  NFB_TerminalCuts.complete start terminal lines flat out ending nonempty last
 obtain ⟨ps,prod,prefixRun,prefixLength⟩ := NFB_PrefixDomain.complete flat (by omega)
 have same : (ps,prod)=(prefixes,product) := Result.ok.inj (prefixRun.symm.trans hp)
 cases same
 obtain ⟨initialQuery,initialFlat,initialLines⟩ := initial_frame heap
 obtain ⟨flatPayload,linePayload⟩ := NFB_GatherFrame.payloads rows (initial heap) [] [] initialFlat initialLines
 have frame := fun count=>NFB_GatherFrame.query_frame rows (initial heap) count
 refine ⟨rows,terminal,lines,flat,prefixes,product,suffix,groups,nrows,hflat,hlines,?_,prefixLength,
  hp,hs,startField,lineField,groupsField,ending,last,?_,?_,?_⟩
 · omega
 · rw [lineField,hlines]
   simpa only [List.nil_append] using linePayload
 · intro count
   exact (frame count).trans initialQuery
 · intro count
   rw [NFB_TerminalFrame.query_frame]
   exact (NFB_PhysicalFrame.trace_frame _ (initial heap) 0
    (fun a ha=>NFB_PrivateFrame.disjoint a (NFB_GatherFrame.owned rows a ha))).trans initialQuery
#print axioms initial_frame
#print axioms complete
end NFB_ReturnedBuffers
end
