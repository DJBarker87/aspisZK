import JGl_ConcreteSelected
import JGl_NumericProbe
import JFu_TerminalPrefix
set_option autoImplicit false
namespace AspisR1.JGl_CutProbe
open Aeneas Aeneas.Std Result FIq_Native
abbrev QM := field.QM31
def a : Array QM 16#usize := ⟨[FIq_Carriers.toQ JFu_ClaimsData.q000,FIq_Carriers.toQ JFu_ClaimsData.q001,FIq_Carriers.toQ JFu_ClaimsData.q002,FIq_Carriers.toQ JFu_ClaimsData.q003,FIq_Carriers.toQ JFu_ClaimsData.q004,FIq_Carriers.toQ JFu_ClaimsData.q005,FIq_Carriers.toQ JFu_ClaimsData.q006,FIq_Carriers.toQ JFu_ClaimsData.q007,FIq_Carriers.toQ JFu_ClaimsData.q008,FIq_Carriers.toQ JFu_ClaimsData.q009,FIq_Carriers.toQ JFu_ClaimsData.q010,FIq_Carriers.toQ JFu_ClaimsData.q011,FIq_Carriers.toQ JFu_ClaimsData.q012,FIq_Carriers.toQ JFu_ClaimsData.q013,FIq_Carriers.toQ JFu_ClaimsData.q014,FIq_Carriers.toQ JFu_ClaimsData.q015],by rfl⟩
def b : Array QM 16#usize := ⟨[FIq_Carriers.toQ JFu_ClaimsData.q029,FIq_Carriers.toQ JFu_ClaimsData.q030,FIq_Carriers.toQ JFu_ClaimsData.q031,FIq_Carriers.toQ JFu_ClaimsData.q032,FIq_Carriers.toQ JFu_ClaimsData.q033,FIq_Carriers.toQ JFu_ClaimsData.q034,FIq_Carriers.toQ JFu_ClaimsData.q035,FIq_Carriers.toQ JFu_ClaimsData.q036,FIq_Carriers.toQ JFu_ClaimsData.q037,FIq_Carriers.toQ JFu_ClaimsData.q038,FIq_Carriers.toQ JFu_ClaimsData.q039,FIq_Carriers.toQ JFu_ClaimsData.q040,FIq_Carriers.toQ JFu_ClaimsData.q041,FIq_Carriers.toQ JFu_ClaimsData.q042,FIq_Carriers.toQ JFu_ClaimsData.q043,FIq_Carriers.toQ JFu_ClaimsData.q044],by rfl⟩
def c : Array QM 16#usize := ⟨[FIq_Carriers.toQ JFu_ClaimsData.q058,FIq_Carriers.toQ JFu_ClaimsData.q059,FIq_Carriers.toQ JFu_ClaimsData.q060,FIq_Carriers.toQ JFu_ClaimsData.q061,FIq_Carriers.toQ JFu_ClaimsData.q062,FIq_Carriers.toQ JFu_ClaimsData.q063,FIq_Carriers.toQ JFu_ClaimsData.q064,FIq_Carriers.toQ JFu_ClaimsData.q065,FIq_Carriers.toQ JFu_ClaimsData.q066,FIq_Carriers.toQ JFu_ClaimsData.q067,FIq_Carriers.toQ JFu_ClaimsData.q068,FIq_Carriers.toQ JFu_ClaimsData.q069,FIq_Carriers.toQ JFu_ClaimsData.q070,FIq_Carriers.toQ JFu_ClaimsData.q071,FIq_Carriers.toQ JFu_ClaimsData.q072,FIq_Carriers.toQ JFu_ClaimsData.q073],by rfl⟩
def ws {N : Usize} (s : Array QM N) := s.val.map (fun q=>(q.c0.a.val,q.c0.b.val,q.c1.a.val,q.c1.b.val))
def probe : Result (List (String × List (Nat × Nat × Nat × Nat))) := do
  let s ← pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point JFu_TerminalPrefix.alpha
  let ps ← pool_v1.pair_forest_semantic_terminal.poseidon_selectors s
  let lp ← state_only_poseidon.leading_pair_packed ⟨a,b,c⟩
  let fp ← state_only_poseidon.interpolated_full_pair_packed a ps.local
  let ip ← state_only_poseidon.interpolated_internal_pair a ps.local
  let pos ← state_only_poseidon.evaluate_state_only_poseidon_oracle_projected ⟨a,b,c⟩ ps
  let sem ← pool_v1.pair_forest_semantic_terminal.semantic_packed JFu_PublicSemantic.value ⟨a,b,c⟩ s
  let cp ← pool_v1.pair_forest_copy_terminal.evaluate_with_selectors a
    (FIq_Carriers.toQ JFu_ClaimsData.q026) s JFu_TerminalPrefix.challenges.lambda
    JFu_TerminalPrefix.challenges.chi JFu_PublicSemantic.value.transition.live_snapshot.next_pair_index .PrivateTransfer
  ok [("high",ws s.high),("low",ws s.low),("block",[JGl_NumericProbe.words (FIq_Carriers.fromQ ps.block)]),
    ("leading",ws lp),("full",ws fp),("internal",ws ip),("poseidon",ws pos),("semantic",ws sem),
    ("copy",[JGl_NumericProbe.words (FIq_Carriers.fromQ cp.residual),JGl_NumericProbe.words (FIq_Carriers.fromQ cp.active)])]
#eval match probe with
  | .ok xs => String.intercalate "\n" (xs.map (fun (name,vs)=>name++":"++
      String.intercalate ";" (vs.map (fun (a,b,c,d)=>toString a++","++toString b++","++toString c++","++toString d))))
  | _ => "failed"
end AspisR1.JGl_CutProbe
