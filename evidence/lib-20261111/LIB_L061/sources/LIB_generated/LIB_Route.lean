import LIB_RouteCarrier
set_option autoImplicit false
noncomputable section
namespace LIB_Route
open RSL
abbrev Child := TX2_240.Args → SdkState → Env → Obs (Except ProgramError Unit × SdkState)
/-- Normal form of the emitted dispatcher on its admitted own-input domain.
All child observations are retained verbatim, including abort/divergence. -/
def process (stage1 stage2 : Child) : Child := fun a s env =>
  if TX2_221.stage1Route a.data then stage1 a s env else stage2 a s env
/-- Entry rejects before touching accounts, otherwise tail-calls process. -/
def entry (f : Child) : Child := fun a s env =>
  if TX2_221.admitted a.data then f a s env
  else ⟨.ret (.error .invalidInstructionData, s), []⟩
theorem admitted_iff (d : Bytes) : TX2_221.admitted d = true ↔
    TX2_221.stage1Route d = true ∨ d.take 4 = REQUEST_MAGIC := by
  simp only [TX2_221.admitted, TX2_221.stage1Route, Bool.or_eq_true, beq_iff_eq]

open Aeneas Aeneas.Std AspisR1 LIB_RouteCarrier
/-- Semantic transport at SAME source arguments. Lifecycle arms are outside
admitted. The source operations decode the actual p/accounts/data supplied by
NMW's emitted call; no child reply or native=model premise occurs here. -/
theorem process_emitted (f1 f2 : Child) (s : SdkState) (env : Env)
    (p : Hiq_DispatchSource.Key) (a : Slice AccountInfo) (d : Slice U8)
    (admitted : TX2_221.admitted (unbytes d.val) = true) :
    NMW_Symbolic.process (ops f1 f2 s env) p a d =
      .ok (process f1 f2 (args p a d) s env) := by
  by_cases h : TX2_221.stage1Route (unbytes d.val) = true
  · rw [NMW_Branches.first _ _ _ _ ((stage1_iff d).mp h)]
    simp only [ops, process, args, h, Bool.true_eq, if_true]
  · have ha := (admitted_iff _).mp admitted
    have hq : (unbytes d.val).take 4 = REQUEST_MAGIC := ha.resolve_left h
    rw [NMW_Branches.second _ _ _ _ ((asq8_iff d).mp hq)]
    simp only [ops, process, args, h, Bool.false_eq_true, if_false]

/-- Full entry transport, including rejection of arbitrary malformed bytes. -/
theorem entry_emitted (f1 f2 : Child) (s : SdkState) (env : Env)
    (p : Hiq_DispatchSource.Key) (a : Slice AccountInfo) (d : Slice U8) :
    NMW_Symbolic.entry (ops f1 f2 s env)
      ⟨.ret (.error .invalidInstructionData, s), []⟩ p a d =
      .ok (entry (process f1 f2) (args p a d) s env) := by
  rw [NMW_Branches.entry_total]
  by_cases h : TX2_221.stage1Route (unbytes d.val) = true
  · have hr := (stage1_iff d).mp h
    have ha := (admitted_iff _).mpr (Or.inl h)
    simp only [Hiq_ReleaseRoute.route, hr, if_true, ops, entry, process, args, ha, h,
      Bool.true_eq]
  · by_cases q : (unbytes d.val).take 4 = REQUEST_MAGIC
    · have hr := (asq8_iff d).mp q
      have hn : ¬ Hiq_ReleaseRoute.stage1 d := fun x => h ((stage1_iff d).mpr x)
      have ha := (admitted_iff _).mpr (Or.inr q)
      simp only [Hiq_ReleaseRoute.route, hn, hr, if_false, if_true, ops, entry, process,
        args, ha, h, Bool.true_eq, Bool.false_eq_true]
    · have hn : ¬ Hiq_ReleaseRoute.stage1 d := fun x => h ((stage1_iff d).mpr x)
      have hq : ¬ Hiq_ReleaseRoute.asq8 d := fun x => q ((asq8_iff d).mpr x)
      have ha : TX2_221.admitted (unbytes d.val) = false := by
        cases had : TX2_221.admitted (unbytes d.val)
        · rfl
        · rcases (admitted_iff _).mp had with x | x
          · exact False.elim (h x)
          · exact False.elim (q x)
      simp only [Hiq_ReleaseRoute.route, hn, hq, if_false, entry, args, ha,
        Bool.false_eq_true]
#print axioms admitted_iff
#print axioms process_emitted
#print axioms entry_emitted
end LIB_Route
end
