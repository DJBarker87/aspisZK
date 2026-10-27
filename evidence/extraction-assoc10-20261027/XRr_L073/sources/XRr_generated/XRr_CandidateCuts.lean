import XRr_Accepted64
open Aeneas Aeneas.Std Result XRn_Join_Release XRk_ResultTools
set_option autoImplicit false
namespace XRr_CandidateCuts
/-- Every witness is projected from THIS compact candidate execution. The
adopted-cohort and native checkpoint associations remain separate. -/
theorem source {H : Type} (D : aspis_core.digest.Digest32 H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (physical proof : Slice U8) (split : Usize) (hash : H)
 (obs : Option (verifier.Phase → Result Unit)) (saved : alloc.vec.Vec U8)
 (run : verifier.candidate.tx1 D pub physical proof split hash obs=ok (.Ok saved)) :
 split=compact.SPLIT ∧
 ∃ (shape : transport.Variant) (zero : aspis_core.field.wide_exact.WideExact)
   (p : verifier.Prepared) (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
   (initial : verifier.Accumulator) (root : Array U8 32#usize)
   (geo : verifier.QueryGeometry) (pending0 : verifier.BatchedWeights)
   (a : verifier.Accumulator) (pending : verifier.BatchedWeights)
   (slice : Slice aspis_core.field.QM31)
   (restore : Slice aspis_core.field.QM31 → alloc.vec.Vec aspis_core.field.QM31)
   (finished : Slice aspis_core.field.QM31),
 verifier.candidate.parse_shape proof=ok (.Ok shape) ∧
 verifier.candidate.canonical_scan proof=ok (.Ok ()) ∧
 aspis_core.field.wide_exact.WideExact.ZERO=ok zero ∧
 verifier.candidate.prepare D pub proof hash obs (Array.repeat 29#usize zero)=ok (.Ok p,g) ∧
 verifier.Accumulator.new .S2=ok (.Ok initial) ∧
 verifier.candidate.batch_merkle D proof p root 0#usize hash=ok (.Ok ()) ∧
 verifier.QueryGeometry.for_range p.queries 0#usize split=ok (.Ok geo) ∧
 verifier.BatchedWeights.new (alloc.vec.Vec.deref initial.weights)=ok (.Ok pending0) ∧
 verifier.candidate.query_loop proof p initial g obs geo pending0 split=ok (.Ok (a,pending)) ∧
 lift (alloc.vec.Vec.deref_mut a.weights)=ok (slice,restore) ∧
 verifier.BatchedWeights.finish pending slice=ok finished ∧
 verifier.checkpoint D p {a with weights:=restore finished} proof physical hash=ok saved := by
 unfold verifier.candidate.tx1 at run
 split at run
 · cases run
 · rename_i hs
   have splitEq : split=compact.SPLIT := by simpa only [bne_iff_ne,not_not] using hs
   refine ⟨splitEq,?_⟩
   obtain ⟨r,hshape,run⟩ := bind_success _ _ _ run
   cases r with
   | Err e => cases run
   | Ok shape =>
     simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
     obtain ⟨r,hscan,run⟩ := bind_success _ _ _ run
     cases r with
     | Err e => cases run
     | Ok unit =>
       cases unit
       simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
       obtain ⟨marked,_,run⟩ := bind_success _ _ _ run
       obtain ⟨zero,hzero,run⟩ := bind_success _ _ _ run
       obtain ⟨r,g,hprepare,run⟩ := pair_bind_success _ _ _ run
       cases r with
       | Err e => cases run
       | Ok p =>
         simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
         obtain ⟨r,hinit,run⟩ := bind_success _ _ _ run
         cases r with
         | Err e => cases run
         | Ok initial =>
           simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
           obtain ⟨marked,_,run⟩ := bind_success _ _ _ run
           obtain ⟨off0,_,run⟩ := bind_success _ _ _ run
           obtain ⟨off1,_,run⟩ := bind_success _ _ _ run
           obtain ⟨rootSlice,_,run⟩ := bind_success _ _ _ run
           obtain ⟨rootResult,_,run⟩ := bind_success _ _ _ run
           obtain ⟨root,_,run⟩ := bind_success _ _ _ run
           obtain ⟨r,hbatch,run⟩ := bind_success _ _ _ run
           cases r with
           | Err e => cases run
           | Ok unit =>
             cases unit
             simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
             obtain ⟨marked,_,run⟩ := bind_success _ _ _ run
             obtain ⟨r,hgeo,run⟩ := bind_success _ _ _ run
             cases r with
             | Err e => cases run
             | Ok geo =>
               simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
               obtain ⟨r,hpending,run⟩ := bind_success _ _ _ run
               cases r with
               | Err e => cases run
               | Ok pending0 =>
                 simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
                 obtain ⟨r,hquery,run⟩ := bind_success _ _ _ run
                 cases r with
                 | Err e => cases run
                 | Ok pair =>
                   rcases pair with ⟨a,pending⟩
                   simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
                   obtain ⟨slice,restore,hrestore,run⟩ := pair_bind_success _ _ _ run
                   obtain ⟨finished,hfinish,run⟩ := bind_success _ _ _ run
                   obtain ⟨bytes,hcheckpoint,run⟩ := bind_success _ _ _ run
                   obtain ⟨marked,_,run⟩ := bind_success _ _ _ run
                   have same : bytes=saved := core.result.Result.Ok.inj (Result.ok.inj run)
                   subst bytes
                   exact ⟨shape,zero,p,g,initial,root,geo,pending0,a,pending,slice,restore,finished,
                     hshape,hscan,hzero,hprepare,hinit,hbatch,hgeo,hpending,hquery,hrestore,hfinish,hcheckpoint⟩
#print axioms source
end XRr_CandidateCuts
