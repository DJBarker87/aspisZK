import NNE_RslOk
import TAS_Interfaces
set_option autoImplicit false
namespace NNE_SelectedRoutes
open RSL RSL.TAS

theorem routes (L : PoolLib) (D : DeployedIds) (V : TX2_241.V2Lib)
 (VL : VLib) (P : PreparedNew VL) (C : TX1_345.S1Lib VL)
 (a : TX2_213.Args) (s post : SdkState) (env : Env) (es : List Event)
 (h : TX2_213.Ref L D V (TX1_344.asStage1 VL P C) a s env ⟨.ret (.ok (),post),es⟩) :
 (a.accounts.length = 3 ∧ TX2_221.stage1Route a.data = true) ∨
 (a.accounts.length = 7 ∧ ASQ8 a.data) := by
 have hadm : TX2_221.admitted a.data = true := by
  cases hb : TX2_221.admitted a.data with
  | true => rfl
  | false => simp [TX2_213.Ref,hb,Spec.pure] at h
 cases hs : TX2_221.stage1Route a.data with
 | true =>
  have h1 := ref213_stage1 hs h
  obtain ⟨_,_,_,_,_,_,_,hg,_⟩ := NNE_RslOk.first_ok VL P C a s post env es h1
  have hn : a.accounts.length = 3 := by
   simp only [TX1_344.badRoute,Bool.or_eq_false_iff,bne_eq_false_iff_eq] at hg
   exact hg.2
  exact .inl ⟨hn,rfl⟩
 | false =>
  have hq : ASQ8 a.data := by
   unfold TX2_221.admitted at hadm
   change (TX2_221.stage1Route a.data || (a.data.take 4 == REQUEST_MAGIC)) = true at hadm
   rw [hs] at hadm
   simpa [ASQ8] using hadm
  have h2 := ref213_asq8 hq h
  obtain ⟨_,_,_,hg,_⟩ := NNE_RslOk.second_ok L D V a s post env es h2
  have hn : a.accounts.length = 7 := by
   simp only [TX2_240.badRoute,Bool.or_eq_false_iff,bne_eq_false_iff_eq] at hg
   exact hg.1.1
  exact .inr ⟨hn,hq⟩

theorem first (L : PoolLib) (D : DeployedIds) (V : TX2_241.V2Lib)
 (VL : VLib) (P : PreparedNew VL) (C : TX1_345.S1Lib VL)
 (a : TX2_213.Args) (s : SdkState) (env : Env) (o : Obs (Except ProgramError Unit × SdkState))
 (count : a.accounts.length = 3)
 (h : TX2_213.Ref L D V (TX1_344.asStage1 VL P C) a s env o)
 (ok : ∃ post, o.exit = .ret (.ok (),post)) : TX2_221.stage1Route a.data = true := by
 obtain ⟨post,hpost⟩ := ok
 cases o with
 | mk exit es =>
  dsimp only at hpost; subst exit
  rcases routes L D V VL P C a s post env es h with h | h
  · exact h.2
  · omega

theorem second (L : PoolLib) (D : DeployedIds) (V : TX2_241.V2Lib)
 (VL : VLib) (P : PreparedNew VL) (C : TX1_345.S1Lib VL)
 (a : TX2_213.Args) (s : SdkState) (env : Env) (o : Obs (Except ProgramError Unit × SdkState))
 (count : a.accounts.length = 7)
 (h : TX2_213.Ref L D V (TX1_344.asStage1 VL P C) a s env o)
 (ok : ∃ post, o.exit = .ret (.ok (),post)) : ASQ8 a.data := by
 obtain ⟨post,hpost⟩ := ok
 cases o with
 | mk exit es =>
  dsimp only at hpost; subst exit
  rcases routes L D V VL P C a s post env es h with h | h
  · omega
  · exact h.2
#print axioms routes
#print axioms first
#print axioms second
end NNE_SelectedRoutes
