import NBA_Installed
import CurrentPreparedScratchReachability
set_option autoImplicit false
noncomputable section
namespace AspisR1.NBA_TraceReplay
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedScratchReachability

/-- Replay of the locally linked calls, in source order. This is a cohort
replay theorem; constructing these observations from native calls is separate. -/
theorem source {H : Type} (D : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H)
    (out : verifier.Prepared) (scratch old : Array aspis_core.field.WideExact 29#usize)
    (trace : Reachable NBA_Installed.actual D sem v hash out scratch) :
    PreparedScratchModel.prepare NBA_Installed.actual D sem v hash old=ok (.Ok out,scratch) := by
  rcases trace with ⟨start,t1,t2,t3,bytes,gamma,kappa,alpha0,hseed,hg,hbytes,hk,ha,tail⟩
  have add_exact {ty : UScalarTy} (a b c : UScalar ty)
      (hc : c.val=a.val+b.val) : a+b=ok c := by
    obtain ⟨z,hz,hval⟩ := WP.spec_imp_exists
      (UScalar.add_spec (x:=a) (y:=b) (by scalar_tac))
    have he : z=c := by scalar_tac
    simpa only [he] using hz
  have cap : (32#usize + 224#usize : Result Usize)=ok 256#usize := add_exact _ _ _ (by scalar_tac)
  have single : (30#u8 + 1#u8 : Result U8)=ok 31#u8 := add_exact _ _ _ (by scalar_tac)
  have double : (31#u8 + 1#u8 : Result U8)=ok 32#u8 := add_exact _ _ _ (by scalar_tac)
  unfold PreparedScratchModel.prepare
  simp only [r1_wire.SemanticTranscript.impl.state,hseed,bind_tc_ok,hg,hbytes,lift,hk,ha]
  dsimp! only
  simp only [hk,bind_tc_ok]
  dsimp! only
  simp only [ha,bind_tc_ok]
  dsimp! only
  cases tail with
  | single hf rest =>
    obtain ⟨qs,afterQueries,last,rho,claim,hq,hr,hp,hc,he⟩ := rest
    have row : (if 30#u8=30#u8 then 31#u8 else 32#u8)=31#u8 := if_pos rfl
    rw [row] at hr
    rw [he]
    simp only [hf,bind_tc_ok,show ¬(1#usize=2#usize) by decide,↓reduceIte,hq,
      core.result.Result.Insts.CoreOpsTry.branch,single,lift,hr,emptyPayload,hp,hc,output]
    dsimp! only
    simp only [hq,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,single,lift]
    dsimp! only
    simp only [←emptyPayload,hr,bind_tc_ok]
    dsimp! only
    simp only [hp,bind_tc_ok,hc,core.result.Result.Insts.CoreOpsTry.branch,output]
  | double hf root b1 b2 alpha1 afterAlpha hroot hb1 hb2 halpha rest =>
    obtain ⟨qs,afterQueries,last,rho,claim,hq,hr,hp,hc,he⟩ := rest
    have row : (if 31#u8=30#u8 then 31#u8 else 32#u8)=32#u8 := if_neg (by decide)
    rw [row] at hr
    rw [he]
    simp only [hf,bind_tc_ok,↓reduceIte,cap,lift,hroot,hb1,hb2,halpha,hq,
      core.result.Result.Insts.CoreOpsTry.branch,double,hr,emptyPayload,hp,hc,output]
    dsimp! only
    simp only [halpha,bind_tc_ok]
    dsimp! only
    simp only [hq,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,double,lift]
    dsimp! only
    simp only [←emptyPayload,hr,bind_tc_ok]
    dsimp! only
    simp only [hp,bind_tc_ok,hc,core.result.Result.Insts.CoreOpsTry.branch,output]

theorem unique {H : Type} (D : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H)
    (left right : verifier.Prepared) (gleft gright old : Array aspis_core.field.WideExact 29#usize)
    (lt : Reachable NBA_Installed.actual D sem v hash left gleft)
    (rt : Reachable NBA_Installed.actual D sem v hash right gright) :
    left=right ∧ gleft=gright := by
  have same := Result.ok.inj ((source D sem v hash left gleft old lt).symm.trans
    (source D sem v hash right gright old rt))
  exact ⟨core.result.Result.Ok.inj (congrArg Prod.fst same),congrArg Prod.snd same⟩

#print axioms source
#print axioms unique
end AspisR1.NBA_TraceReplay
end
