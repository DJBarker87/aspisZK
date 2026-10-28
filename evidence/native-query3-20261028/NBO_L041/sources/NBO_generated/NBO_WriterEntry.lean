import NBO_EveryCaller
set_option autoImplicit false
noncomputable section
namespace NBO_WriterEntry
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2 Port3_NativeQueryBody
/-- Bind the complete checked composite to the SAME actual writer input.
All constructors, preparation, geometry, query and flush cuts are extracted
from that one prefix. No second accepted execution or output is introduced. -/
theorem same_writer (base : VTop_Stages.Ops) (reserved : Bool) (ops : Ops)
 (producers : NBO_ProducerDomains.NBA_NBC base ops) (bounds : NBO_Entry.NBC_Bounds base)
 (lower : NBO_QueryDomains.Lower ops) (bindings : NBO_FieldSemantics.NBC_Bindings ops)
 {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
 (semantic : VTop_Stages.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (proof : Slice U8) (split : Usize) (p : verifier.Prepared) (a : verifier.Accumulator)
 (reached : VTop_Provenance.WriterPrefix (NBO_TopInstall.install base reserved ops)
   D hash semantic proof split none p a) :
 ∃ g initial pending geometry after,
 NBO_Entry.Prelude base reserved D hash semantic proof split p g initial pending geometry ∧
 NBO_Composite.source ops proof p initial g geometry pending=ok (.Ok (a,after)) ∧
 NBO_Composite.reference ops proof p initial g geometry pending=ok (.Ok (a,after)) := by
 obtain ⟨zero,g,prep,initial,root,geometry,pending,returned,flushed,parsed,sv,
   hs,hsv,hparse,hscan,hzero,hprep,hbranch,hinit,hbatch,hgeom,hpending,hquery,hflush,
   hw,hr,hp,hn⟩ := reached
 have split10 : split.val=10 := by
   have same : (10#usize : Usize)=sv := Result.ok.inj hs
   subst sv;exact hsv
 have splitEq : split=10#usize := UScalar.eq_of_val_eq split10
 have entry : NBO_Entry.Prelude base reserved D hash semantic proof split p g initial pending geometry :=
   ⟨zero,prep,root,parsed,split10,hparse,hscan,hzero,hprep,hbranch,hinit,hbatch,hgeom,hpending⟩
 have query : verifier.candidate.query_loop (NBF_Accumulate.install ops)
   proof p initial g none geometry pending 10#usize=ok (.Ok returned) := by
   change NBO_TopInstall.query ops proof p initial g none geometry pending split=_ at hquery
   unfold NBO_TopInstall.query at hquery
   have h:=(Port3_QueryInstall.success_iff _ _).mp hquery
   simpa only [Port3_QueryInstall.observer,Option.map_none,splitEq] using h
 have weightsEq : (⟨flushed.val,flushed.property⟩ : alloc.vec.Vec NBF_RowInstall.Q)=a.weights :=
   Subtype.ext hw.symm
 have same : ({returned.1 with weights:=⟨flushed.val,flushed.property⟩} : verifier.Accumulator)=a := by
   change (⟨(⟨flushed.val,flushed.property⟩ : alloc.vec.Vec NBF_RowInstall.Q),
     returned.1.rhs,returned.1.power,returned.1.next⟩ : verifier.Accumulator)=a
   rw [weightsEq,←hr,←hp,←hn]
 have source : NBO_Composite.source ops proof p initial g geometry pending=ok (.Ok (a,returned.2)) := by
   simp only [NBO_Composite.source,query,NBO_Composite.finishResult,bind_tc_ok,hflush,same]
 have assoc:=NBO_Entry.association base reserved ops producers bounds lower bindings D hash semantic
   proof split p g initial pending geometry entry
 exact ⟨g,initial,pending,geometry,returned.2,entry,source,assoc.symm.trans source⟩
#print axioms same_writer
end NBO_WriterEntry
end
