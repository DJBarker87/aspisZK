import NNE_SelectedRoutes
set_option autoImplicit false
namespace NNE_SelectedContext
open RSL RSL.TAS

def pullback (S : Sig) {Ctx : Type} (q : Ctx → S.Ctx) : Sig where
 Ctx := Ctx
 First := S.First
 Second := S.Second
 model1 := fun c => S.model1 (q c)
 model2 := fun c => S.model2 (q c)
 Exhibited := fun c => S.Exhibited (q c)
 Extraction := fun c => S.Extraction (q c)
 Accepted1 := fun c => S.Accepted1 (q c)
 Accepted2 := fun c => S.Accepted2 (q c)
 GameFrame := fun c => S.GameFrame (q c)
 Recorded1 := fun c => S.Recorded1 (q c)
 Recorded2 := fun c => S.Recorded2 (q c)
 Game := fun c => S.Game (q c)
 mkGame := fun c => S.mkGame (q c)
 Queries := fun c => S.Queries (q c)
 Concl := fun c => S.Concl (q c)
 Bound := fun c => S.Bound (q c)
 Event := fun c => S.Event (q c)
 args1 := fun c => S.args1 (q c)
 args2 := fun c => S.args2 (q c)
 state1 := fun c => S.state1 (q c)
 state2 := fun c => S.state2 (q c)
 env1 := fun c => S.env1 (q c)
 env2 := fun c => S.env2 (q c)
 Out1 := fun c => S.Out1 (q c)
 Out2 := fun c => S.Out2 (q c)
 EnvRep := fun c => S.EnvRep (q c)
 env1_rep := fun c => S.env1_rep (q c)
 env2_rep := fun c => S.env2_rep (q c)
 TraceRep := fun c => S.TraceRep (q c)
 Root0Native := fun c => S.Root0Native (q c)
 readerHeader := S.readerHeader
 ModelRet1 := fun c => S.ModelRet1 (q c)
 ModelRet2 := fun c => S.ModelRet2 (q c)

/-- Reindex by the two actual returned-Ok antecedents already required by TAS
and TFM. This contains no model acceptance or allocator-success premise. -/
structure Selected (S : Sig) {L : PoolLib} {V0 : TX2_241.V2Lib} {VL : VLib} (I : Impl L V0 VL) where
 base : S.Ctx
 ok1 : ∃ post, (I.entry (S.args1 base) (S.state1 base) (S.env1 base)).exit = .ret (.ok (),post)
 ok2 : ∃ post, (I.entry (S.args2 base) (S.state2 base) (S.env2 base)).exit = .ret (.ok (),post)

def sig (S : Sig) {L : PoolLib} {V0 : TX2_241.V2Lib} {VL : VLib} (I : Impl L V0 VL) : Sig :=
 pullback S (fun c : Selected S I => c.base)

/-- EXACT TAS entry-representation field, using successful selected occurrences
as actual-input context, never as a new trust or model-success hypothesis. -/
def packet (S : Sig) (L : PoolLib) (D : DeployedIds) (V0 : TX2_241.V2Lib)
 (VL : VLib) (P : PreparedNew VL) (C : TX1_345.S1Lib VL) (I : Impl L V0 VL)
 (V : TX2_241.V2Lib)
 (weak : ∀ a s env, TX2_213.Ref L D V (TX1_344.asStage1 VL P C) a s env (I.entry a s env))
 (count1 : ∀ c, (S.args1 c).accounts.length = 3)
 (count2 : ∀ c, (S.args2 c).accounts.length = 7) :
 NNE_EntryRep (sig S I) L V0 VL I where
 route1 := fun c _ _ => NNE_SelectedRoutes.first L D V VL P C _ _ _ _
   (count1 c.base) (weak _ _ _) c.ok1
 route2 := fun c _ _ => NNE_SelectedRoutes.second L D V VL P C _ _ _ _
   (count2 c.base) (weak _ _ _) c.ok2

theorem covers (S : Sig) {L : PoolLib} {V0 : TX2_241.V2Lib} {VL : VLib} (I : Impl L V0 VL)
 (c : S.Ctx)
 (ok1 : ∃ post, (I.entry (S.args1 c) (S.state1 c) (S.env1 c)).exit = .ret (.ok (),post))
 (ok2 : ∃ post, (I.entry (S.args2 c) (S.state2 c) (S.env2 c)).exit = .ret (.ok (),post)) :
 ∃ selected : Selected S I, selected.base = c := ⟨⟨c,ok1,ok2⟩,rfl⟩
#print axioms packet
#print axioms covers
end NNE_SelectedContext
