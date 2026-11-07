import NNG_PrepareOrigin094
import NNG_PreparedReturned094
import NNG_FrontOrigin094
import NNG_FrontFields094
import NNG_FrontPrefix094
import NNG_ObservedAt094
import NNG_ObservedRoots094
import NNG_PreparedFields094
import NNG_ReadyFront087
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_PrepareFacts094
open Aeneas Aeneas.Std Result NMP_prepare NMP_Emitted
abbrev Args := NNG_PrepareInput087.Args

theorem reserved (env : RSL.Env) (s : Parent Unit Unit) (sem : r1_semantic.Verified Unit) (v : verifier.View)
 (front : NNG_FrontValue087.tree (NNG_PrepareEmission087.calls env) s=.ok (.Ok (sem,v))) :
 env.reservation=true := by
 unfold NNG_FrontValue087.tree at front
 obtain ⟨reply,filled,tail⟩ := NNG_ModelSuccess136.bind_out _ _ _ front
 cases reply with
 | Err e=>cases tail
 | Ok logical=>
   change NNG_Filled087.call env core.marker.CopyU8 14759#usize 0#u8=.ok (.Ok logical) at filled
   unfold NNG_Filled087.call at filled
   cases h : env.reservation with
   | false=>simp only [h,Bool.false_eq_true,if_false] at filled;cases filled
   | true=>rfl
#print axioms reserved

/-- Full child-result facts from the SAME actual prepare return. All internal
semantic, compact, scratch and field domains are discharged here. -/
theorem returned (a : Args) (obs : RSL.Observer) (env : RSL.Env)
 (domain : RSL.TX1_087.Domain LIB_Instances.VL a obs)
 (p : verifier.Prepared) (g : Scratch)
 (native : NMP_Emitted.prepare (NNG_PrepareEmission087.calls env) (NNG_PrepareInput087.input a obs env)=.ok (.Ok p,g)) :
 ∃ input ev,
 LIBC_PreparedLaw.law input env
  ⟨.ret (.ok (NNG_PrepareCarriers087.prepared p),NMT_Transport.arr NNG_PrepareCarriers087.wide g),ev⟩ ∧
 NGC_PreparationBoundary.Fields (NFW_PreparedPort.prepared (NNG_PrepareCarriers087.prepared p)) ∧
 ∃ root0 root1,(NNG_PrepareCarriers087.prepared p).roots=Array.make 2#usize [root0,root1] ∧
 root0.val=((NNG_PrepareInput087.input a obs env).bytes.val.drop 16).take 32 := by
 let s:=NNG_PrepareInput087.input a obs env
 obtain ⟨sem,v,front,prepared⟩ := NNG_PrepareOrigin094.returned env s p g native
 have ready := NNG_ReadyFront087.returned a obs env domain sem v front
 have origin := NNG_FrontOrigin094.returned env s sem v front
 have semanticFields := NNG_FrontFields094.returned env s sem v front
 have prefixFields := NNG_FrontPrefix094.returned a obs env domain sem v front
 have semantic := NNG_ObservedAt094.returned env _ sem origin rfl (reserved env s sem v front)
 obtain ⟨ev,law⟩ := NNG_PreparedReturned094.law env sem v s.scratch g p prepared
 let input : LIBC_PreparedLaw.Args :=
  (NMP_Transport.toT11 sem,NNG_PrepareCarriers087.view v,NMT_Transport.arr NNG_PrepareCarriers087.wide s.scratch)
 have own : LIBC_PreparedDomain.Domain input := ready.2
 have variant : (NNG_PrepareCarriers087.view v).variant=.S2 := by
  change NNG_PrepareCarriers087.variant v.variant=.S2
  rw [prefixFields.2]
  rfl
 have fields := NNG_PreparedFields094.reached input env (NNG_PrepareCarriers087.prepared p)
  (NMT_Transport.arr NNG_PrepareCarriers087.wide g) ev semantic own variant
  semanticFields.1 semanticFields.2 law
 have copies := NNG_PreparedCopies094.copied input env (NNG_PrepareCarriers087.prepared p)
  (NMT_Transport.arr NNG_PrepareCarriers087.wide g) ev law
 obtain ⟨root0,root1,roots,rootBytes⟩ := NNG_ObservedRoots094.returned env _ sem origin
 exact ⟨input,ev,law,fields,root0,root1,copies.2.1.trans roots,rootBytes.trans prefixFields.1⟩
#print axioms returned
end AspisR1.NNG_PrepareFacts094
