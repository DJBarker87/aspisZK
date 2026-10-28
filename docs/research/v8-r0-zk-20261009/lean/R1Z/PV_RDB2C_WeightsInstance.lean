import R1Z.PV_RDB2C_SamplerInstance
import R1Z.PV_RDB2C_PV_B2_F_MaterializeRequest
import R1Z.PV_RDB2C_PV_B2_C_ConstructorSuccess
import R1Z.PV_RDB2C_PV_B2_F_AllocationEffects
import R1Z.PV_RDB2C_PV_B2_F_MaterializeFrozen

section
-- Unchanged source component: R1Z.PV_B2_F_MaterializeNative
set_option autoImplicit false
noncomputable section
namespace PV_B2_F_MaterializeNative
open Aeneas Aeneas.Std Result
open PV_B2_C_MutationStep
abbrev Native := ProverRwFull.aspis_core.field.wide_exact.WideExact
abbrev W := PV_B2_251c1.host_weights.Weights
abbrev Outcome := PV_B2_F_AllocationTransport.Outcome

def toNative (v : E) : Native :=
  ⟨⟨⟨v.c0.c0.a,v.c0.c0.b⟩,⟨v.c0.c1.a,v.c0.c1.b⟩⟩,
   ⟨⟨v.c1.c0.a,v.c1.c0.b⟩,⟨v.c1.c1.a,v.c1.c1.b⟩⟩⟩
def fromNative (v : Native) : E :=
  ⟨⟨⟨v.c0.c0.a,v.c0.c0.b⟩,⟨v.c0.c1.a,v.c0.c1.b⟩⟩,
   ⟨⟨v.c1.c0.a,v.c1.c0.b⟩,⟨v.c1.c1.a,v.c1.c1.b⟩⟩⟩
theorem roundtrip (v : E) : fromNative (toNative v)=v := by cases v; rfl
theorem roundtrip_native (v : Native) : toNative (fromNative v)=v := by cases v; rfl

def toVec (out : Out) : alloc.vec.Vec Native :=
  ⟨out.val.map toNative,by rw [List.length_map,out.property]; scalar_tac⟩
def toError : PV_B2_251c1.verifier.Error → ProverRwFull.verifier.Error
  | .Parse => .Parse
  | .Semantic => .Semantic
  | .Transcript => .Transcript
  | .Relation => .Relation
  | .Merkle => .Merkle
  | .Query => .Query
  | .Checkpoint => .Checkpoint
  | .Allocation => .Allocation
  | .Rejected => .Rejected
  | .AttemptsExhausted => .AttemptsExhausted
  | .Entropy => .Entropy
def mapRust : PV_B2_F_AllocationTransport.RustResult →
    core.result.Result (alloc.vec.Vec Native) ProverRwFull.verifier.Error
  | .Ok out => .Ok (toVec out)
  | .Err e => .Err (toError e)

@[reducible] def types (base : ProverRwFull.ExternalTypes) : ProverRwFull.ExternalTypes :=
  {base with op25 := W}

def callback (event : Result Outcome) (w : W) (kappa : Native) :
    Result (core.result.Result (alloc.vec.Vec Native) ProverRwFull.verifier.Error) :=
  PV_B2_E_OrdinaryOriginal.mapResult mapRust
    (PV_B2_F_AllocationEffects.copied event w (fromNative kappa))
def originalCallback (event : Result Outcome) (w : W) (kappa : Native) :
    Result (core.result.Result (alloc.vec.Vec Native) ProverRwFull.verifier.Error) :=
  PV_B2_E_OrdinaryOriginal.mapResult mapRust
    ((event >>= fun outcome => PV_B2_F_MaterializeFrozen.original outcome w (fromNative kappa)))

def selected (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) : @ProverRwFull.ExternalFuns (types base) :=
  letI : ProverRwFull.ExternalTypes := types base
  {@PV_B2_E_GammaOriginal.selected (types base) ops with op251 := callback event}
def originalDictionary (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) : @ProverRwFull.ExternalFuns (types base) :=
  letI : ProverRwFull.ExternalTypes := types base
  {@PV_B2_E_GammaOriginal.originalDictionary (types base) ops with op251 := originalCallback event}

theorem callbacks (event : Result Outcome) (w : W) (kappa : Native) :
    callback event w kappa = originalCallback event w kappa := by
  unfold callback originalCallback
  apply congrArg (PV_B2_E_OrdinaryOriginal.mapResult mapRust)
  rw [PV_B2_F_AllocationEffects.complete_result]
  unfold PV_B2_F_AllocationEffects.original
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro outcome _
  exact PV_B2_F_MaterializeFrozen.originals outcome w (fromNative kappa)

theorem selected_callback (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) (w : W) (kappa : Native) :
    @ProverRwFull.ExternalFuns.op251 (types base) (selected base event ops) w kappa = originalCallback event w kappa :=
  callbacks event w kappa

theorem nonvacuity (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (types base)) (w : W) (kappa : Native) :
    ∃ out, @ProverRwFull.ExternalFuns.op251 (types base) (selected base (ok .supplied) ops) w kappa = ok (.Ok out) := by
  obtain ⟨out,ho⟩ := PV_B2_F_AllocationEffects.supplied w (fromNative kappa)
  exact ⟨toVec out,by change PV_B2_E_OrdinaryOriginal.mapResult mapRust _ = _; rw [ho]; rfl⟩

theorem allocation_error (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (types base)) (w : W) (kappa : Native) :
    @ProverRwFull.ExternalFuns.op251 (types base) (selected base (ok .denied) ops) w kappa = ok (.Err ProverRwFull.verifier.Error.Allocation) := rfl

theorem dictionaries (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    selected base event ops = originalDictionary base event ops := by
  have hc : callback event = originalCallback event := by
    funext w kappa
    exact callbacks event w kappa
  unfold selected originalDictionary
  rw [@PV_B2_E_GammaOriginal.dictionaries (types base) ops,hc]

theorem observations {O : Sort _} (base : ProverRwFull.ExternalTypes)
    (observe : @ProverRwFull.ExternalFuns (types base) → O) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    observe (selected base event ops)=observe (originalDictionary base event ops) :=
  congrArg observe (dictionaries base event ops)
theorem preserved_0 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op0 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op0 (types base) ops := @PV_B2_E_GammaOriginal.preserved_0 (types base) ops
theorem preserved_1 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op1 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op1 (types base) ops := @PV_B2_E_GammaOriginal.preserved_1 (types base) ops
theorem preserved_2 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op2 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op2 (types base) ops := @PV_B2_E_GammaOriginal.preserved_2 (types base) ops
theorem preserved_3 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op3 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op3 (types base) ops := @PV_B2_E_GammaOriginal.preserved_3 (types base) ops
theorem preserved_4 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op4 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op4 (types base) ops := @PV_B2_E_GammaOriginal.preserved_4 (types base) ops
theorem preserved_5 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op5 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op5 (types base) ops := @PV_B2_E_GammaOriginal.preserved_5 (types base) ops
theorem preserved_6 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op6 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op6 (types base) ops := @PV_B2_E_GammaOriginal.preserved_6 (types base) ops
theorem preserved_7 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op7 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op7 (types base) ops := @PV_B2_E_GammaOriginal.preserved_7 (types base) ops
theorem preserved_8 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op8 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op8 (types base) ops := @PV_B2_E_GammaOriginal.preserved_8 (types base) ops
theorem preserved_9 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op9 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op9 (types base) ops := @PV_B2_E_GammaOriginal.preserved_9 (types base) ops
theorem preserved_10 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op10 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op10 (types base) ops := @PV_B2_E_GammaOriginal.preserved_10 (types base) ops
theorem preserved_11 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op11 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op11 (types base) ops := @PV_B2_E_GammaOriginal.preserved_11 (types base) ops
theorem preserved_12 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op12 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op12 (types base) ops := @PV_B2_E_GammaOriginal.preserved_12 (types base) ops
theorem preserved_13 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op13 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op13 (types base) ops := @PV_B2_E_GammaOriginal.preserved_13 (types base) ops
theorem preserved_14 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op14 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op14 (types base) ops := @PV_B2_E_GammaOriginal.preserved_14 (types base) ops
theorem preserved_15 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op15 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op15 (types base) ops := @PV_B2_E_GammaOriginal.preserved_15 (types base) ops
theorem preserved_16 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op16 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op16 (types base) ops := @PV_B2_E_GammaOriginal.preserved_16 (types base) ops
theorem preserved_17 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op17 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op17 (types base) ops := @PV_B2_E_GammaOriginal.preserved_17 (types base) ops
theorem preserved_18 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op18 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op18 (types base) ops := @PV_B2_E_GammaOriginal.preserved_18 (types base) ops
theorem preserved_19 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op19 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op19 (types base) ops := @PV_B2_E_GammaOriginal.preserved_19 (types base) ops
theorem preserved_20 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op20 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op20 (types base) ops := @PV_B2_E_GammaOriginal.preserved_20 (types base) ops
theorem preserved_21 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op21 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op21 (types base) ops := @PV_B2_E_GammaOriginal.preserved_21 (types base) ops
theorem preserved_22 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op22 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op22 (types base) ops := @PV_B2_E_GammaOriginal.preserved_22 (types base) ops
theorem preserved_23 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op23 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op23 (types base) ops := @PV_B2_E_GammaOriginal.preserved_23 (types base) ops
theorem preserved_24 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op24 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op24 (types base) ops := @PV_B2_E_GammaOriginal.preserved_24 (types base) ops
theorem preserved_25 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op25 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op25 (types base) ops := @PV_B2_E_GammaOriginal.preserved_25 (types base) ops
theorem preserved_26 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op26 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op26 (types base) ops := @PV_B2_E_GammaOriginal.preserved_26 (types base) ops
theorem preserved_27 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op27 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op27 (types base) ops := @PV_B2_E_GammaOriginal.preserved_27 (types base) ops
theorem preserved_28 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op28 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op28 (types base) ops := @PV_B2_E_GammaOriginal.preserved_28 (types base) ops
theorem preserved_29 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op29 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op29 (types base) ops := @PV_B2_E_GammaOriginal.preserved_29 (types base) ops
theorem preserved_30 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op30 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op30 (types base) ops := @PV_B2_E_GammaOriginal.preserved_30 (types base) ops
theorem preserved_31 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op31 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op31 (types base) ops := @PV_B2_E_GammaOriginal.preserved_31 (types base) ops
theorem preserved_32 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op32 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op32 (types base) ops := @PV_B2_E_GammaOriginal.preserved_32 (types base) ops
theorem preserved_33 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op33 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op33 (types base) ops := @PV_B2_E_GammaOriginal.preserved_33 (types base) ops
theorem preserved_34 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op34 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op34 (types base) ops := @PV_B2_E_GammaOriginal.preserved_34 (types base) ops
theorem preserved_35 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op35 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op35 (types base) ops := @PV_B2_E_GammaOriginal.preserved_35 (types base) ops
theorem preserved_36 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op36 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op36 (types base) ops := @PV_B2_E_GammaOriginal.preserved_36 (types base) ops
theorem preserved_37 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op37 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op37 (types base) ops := @PV_B2_E_GammaOriginal.preserved_37 (types base) ops
theorem preserved_38 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op38 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op38 (types base) ops := @PV_B2_E_GammaOriginal.preserved_38 (types base) ops
theorem preserved_39 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op39 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op39 (types base) ops := @PV_B2_E_GammaOriginal.preserved_39 (types base) ops
theorem preserved_40 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op40 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op40 (types base) ops := @PV_B2_E_GammaOriginal.preserved_40 (types base) ops
theorem preserved_41 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op41 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op41 (types base) ops := @PV_B2_E_GammaOriginal.preserved_41 (types base) ops
theorem preserved_42 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op42 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op42 (types base) ops := @PV_B2_E_GammaOriginal.preserved_42 (types base) ops
theorem preserved_43 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op43 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op43 (types base) ops := @PV_B2_E_GammaOriginal.preserved_43 (types base) ops
theorem preserved_44 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op44 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op44 (types base) ops := @PV_B2_E_GammaOriginal.preserved_44 (types base) ops
theorem preserved_45 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op45 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op45 (types base) ops := @PV_B2_E_GammaOriginal.preserved_45 (types base) ops
theorem preserved_46 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op46 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op46 (types base) ops := @PV_B2_E_GammaOriginal.preserved_46 (types base) ops
theorem preserved_47 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op47 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op47 (types base) ops := @PV_B2_E_GammaOriginal.preserved_47 (types base) ops
theorem preserved_48 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op48 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op48 (types base) ops := @PV_B2_E_GammaOriginal.preserved_48 (types base) ops
theorem preserved_49 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op49 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op49 (types base) ops := @PV_B2_E_GammaOriginal.preserved_49 (types base) ops
theorem preserved_50 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op50 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op50 (types base) ops := @PV_B2_E_GammaOriginal.preserved_50 (types base) ops
theorem preserved_51 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op51 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op51 (types base) ops := @PV_B2_E_GammaOriginal.preserved_51 (types base) ops
theorem preserved_52 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op52 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op52 (types base) ops := @PV_B2_E_GammaOriginal.preserved_52 (types base) ops
theorem preserved_53 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op53 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op53 (types base) ops := @PV_B2_E_GammaOriginal.preserved_53 (types base) ops
theorem preserved_54 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op54 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op54 (types base) ops := @PV_B2_E_GammaOriginal.preserved_54 (types base) ops
theorem preserved_55 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op55 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op55 (types base) ops := @PV_B2_E_GammaOriginal.preserved_55 (types base) ops
theorem preserved_56 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op56 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op56 (types base) ops := @PV_B2_E_GammaOriginal.preserved_56 (types base) ops
theorem preserved_57 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op57 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op57 (types base) ops := @PV_B2_E_GammaOriginal.preserved_57 (types base) ops
theorem preserved_58 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op58 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op58 (types base) ops := @PV_B2_E_GammaOriginal.preserved_58 (types base) ops
theorem preserved_59 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op59 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op59 (types base) ops := @PV_B2_E_GammaOriginal.preserved_59 (types base) ops
theorem preserved_60 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op60 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op60 (types base) ops := @PV_B2_E_GammaOriginal.preserved_60 (types base) ops
theorem preserved_61 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op61 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op61 (types base) ops := @PV_B2_E_GammaOriginal.preserved_61 (types base) ops
theorem preserved_62 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op62 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op62 (types base) ops := @PV_B2_E_GammaOriginal.preserved_62 (types base) ops
theorem preserved_63 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op63 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op63 (types base) ops := @PV_B2_E_GammaOriginal.preserved_63 (types base) ops
theorem preserved_64 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op64 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op64 (types base) ops := @PV_B2_E_GammaOriginal.preserved_64 (types base) ops
theorem preserved_65 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op65 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op65 (types base) ops := @PV_B2_E_GammaOriginal.preserved_65 (types base) ops
theorem preserved_66 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op66 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op66 (types base) ops := @PV_B2_E_GammaOriginal.preserved_66 (types base) ops
theorem preserved_67 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op67 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op67 (types base) ops := @PV_B2_E_GammaOriginal.preserved_67 (types base) ops
theorem preserved_68 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op68 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op68 (types base) ops := @PV_B2_E_GammaOriginal.preserved_68 (types base) ops
theorem preserved_69 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op69 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op69 (types base) ops := @PV_B2_E_GammaOriginal.preserved_69 (types base) ops
theorem preserved_70 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op70 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op70 (types base) ops := @PV_B2_E_GammaOriginal.preserved_70 (types base) ops
theorem preserved_71 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op71 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op71 (types base) ops := @PV_B2_E_GammaOriginal.preserved_71 (types base) ops
theorem preserved_72 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op72 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op72 (types base) ops := @PV_B2_E_GammaOriginal.preserved_72 (types base) ops
theorem preserved_73 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op73 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op73 (types base) ops := @PV_B2_E_GammaOriginal.preserved_73 (types base) ops
theorem preserved_74 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op74 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op74 (types base) ops := @PV_B2_E_GammaOriginal.preserved_74 (types base) ops
theorem preserved_75 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op75 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op75 (types base) ops := @PV_B2_E_GammaOriginal.preserved_75 (types base) ops
theorem preserved_76 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op76 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op76 (types base) ops := @PV_B2_E_GammaOriginal.preserved_76 (types base) ops
theorem preserved_77 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op77 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op77 (types base) ops := @PV_B2_E_GammaOriginal.preserved_77 (types base) ops
theorem preserved_78 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op78 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op78 (types base) ops := @PV_B2_E_GammaOriginal.preserved_78 (types base) ops
theorem preserved_79 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op79 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op79 (types base) ops := @PV_B2_E_GammaOriginal.preserved_79 (types base) ops
theorem preserved_80 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op80 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op80 (types base) ops := @PV_B2_E_GammaOriginal.preserved_80 (types base) ops
theorem preserved_81 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op81 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op81 (types base) ops := @PV_B2_E_GammaOriginal.preserved_81 (types base) ops
theorem preserved_82 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op82 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op82 (types base) ops := @PV_B2_E_GammaOriginal.preserved_82 (types base) ops
theorem preserved_83 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op83 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op83 (types base) ops := @PV_B2_E_GammaOriginal.preserved_83 (types base) ops
theorem preserved_84 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op84 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op84 (types base) ops := @PV_B2_E_GammaOriginal.preserved_84 (types base) ops
theorem preserved_85 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op85 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op85 (types base) ops := @PV_B2_E_GammaOriginal.preserved_85 (types base) ops
theorem preserved_86 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op86 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op86 (types base) ops := @PV_B2_E_GammaOriginal.preserved_86 (types base) ops
theorem preserved_87 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op87 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op87 (types base) ops := @PV_B2_E_GammaOriginal.preserved_87 (types base) ops
theorem preserved_88 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op88 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op88 (types base) ops := @PV_B2_E_GammaOriginal.preserved_88 (types base) ops
theorem preserved_89 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op89 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op89 (types base) ops := @PV_B2_E_GammaOriginal.preserved_89 (types base) ops
theorem preserved_90 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op90 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op90 (types base) ops := @PV_B2_E_GammaOriginal.preserved_90 (types base) ops
theorem preserved_91 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op91 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op91 (types base) ops := @PV_B2_E_GammaOriginal.preserved_91 (types base) ops
theorem preserved_92 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op92 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op92 (types base) ops := @PV_B2_E_GammaOriginal.preserved_92 (types base) ops
theorem preserved_93 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op93 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op93 (types base) ops := @PV_B2_E_GammaOriginal.preserved_93 (types base) ops
theorem preserved_94 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op94 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op94 (types base) ops := @PV_B2_E_GammaOriginal.preserved_94 (types base) ops
theorem preserved_95 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op95 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op95 (types base) ops := @PV_B2_E_GammaOriginal.preserved_95 (types base) ops
theorem preserved_96 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op96 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op96 (types base) ops := @PV_B2_E_GammaOriginal.preserved_96 (types base) ops
theorem preserved_97 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op97 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op97 (types base) ops := @PV_B2_E_GammaOriginal.preserved_97 (types base) ops
theorem preserved_98 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op98 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op98 (types base) ops := @PV_B2_E_GammaOriginal.preserved_98 (types base) ops
theorem preserved_99 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op99 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op99 (types base) ops := @PV_B2_E_GammaOriginal.preserved_99 (types base) ops
theorem preserved_100 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op100 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op100 (types base) ops := @PV_B2_E_GammaOriginal.preserved_100 (types base) ops
theorem preserved_101 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op101 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op101 (types base) ops := @PV_B2_E_GammaOriginal.preserved_101 (types base) ops
theorem preserved_102 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op102 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op102 (types base) ops := @PV_B2_E_GammaOriginal.preserved_102 (types base) ops
theorem preserved_103 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op103 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op103 (types base) ops := @PV_B2_E_GammaOriginal.preserved_103 (types base) ops
theorem preserved_104 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op104 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op104 (types base) ops := @PV_B2_E_GammaOriginal.preserved_104 (types base) ops
theorem preserved_105 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op105 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op105 (types base) ops := @PV_B2_E_GammaOriginal.preserved_105 (types base) ops
theorem preserved_106 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op106 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op106 (types base) ops := @PV_B2_E_GammaOriginal.preserved_106 (types base) ops
theorem preserved_107 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op107 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op107 (types base) ops := @PV_B2_E_GammaOriginal.preserved_107 (types base) ops
theorem preserved_108 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op108 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op108 (types base) ops := @PV_B2_E_GammaOriginal.preserved_108 (types base) ops
theorem preserved_109 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op109 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op109 (types base) ops := @PV_B2_E_GammaOriginal.preserved_109 (types base) ops
theorem preserved_110 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op110 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op110 (types base) ops := @PV_B2_E_GammaOriginal.preserved_110 (types base) ops
theorem preserved_111 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op111 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op111 (types base) ops := @PV_B2_E_GammaOriginal.preserved_111 (types base) ops
theorem preserved_112 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op112 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op112 (types base) ops := @PV_B2_E_GammaOriginal.preserved_112 (types base) ops
theorem preserved_113 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op113 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op113 (types base) ops := @PV_B2_E_GammaOriginal.preserved_113 (types base) ops
theorem preserved_114 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op114 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op114 (types base) ops := @PV_B2_E_GammaOriginal.preserved_114 (types base) ops
theorem preserved_115 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op115 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op115 (types base) ops := @PV_B2_E_GammaOriginal.preserved_115 (types base) ops
theorem preserved_116 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op116 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op116 (types base) ops := @PV_B2_E_GammaOriginal.preserved_116 (types base) ops
theorem preserved_117 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op117 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op117 (types base) ops := @PV_B2_E_GammaOriginal.preserved_117 (types base) ops
theorem preserved_118 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op118 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op118 (types base) ops := @PV_B2_E_GammaOriginal.preserved_118 (types base) ops
theorem preserved_119 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op119 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op119 (types base) ops := @PV_B2_E_GammaOriginal.preserved_119 (types base) ops
theorem preserved_120 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op120 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op120 (types base) ops := @PV_B2_E_GammaOriginal.preserved_120 (types base) ops
theorem preserved_121 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op121 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op121 (types base) ops := @PV_B2_E_GammaOriginal.preserved_121 (types base) ops
theorem preserved_122 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op122 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op122 (types base) ops := @PV_B2_E_GammaOriginal.preserved_122 (types base) ops
theorem preserved_123 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op123 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op123 (types base) ops := @PV_B2_E_GammaOriginal.preserved_123 (types base) ops
theorem preserved_124 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op124 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op124 (types base) ops := @PV_B2_E_GammaOriginal.preserved_124 (types base) ops
theorem preserved_125 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op125 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op125 (types base) ops := @PV_B2_E_GammaOriginal.preserved_125 (types base) ops
theorem preserved_126 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op126 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op126 (types base) ops := @PV_B2_E_GammaOriginal.preserved_126 (types base) ops
theorem preserved_127 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op127 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op127 (types base) ops := @PV_B2_E_GammaOriginal.preserved_127 (types base) ops
theorem preserved_128 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op128 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op128 (types base) ops := @PV_B2_E_GammaOriginal.preserved_128 (types base) ops
theorem preserved_129 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op129 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op129 (types base) ops := @PV_B2_E_GammaOriginal.preserved_129 (types base) ops
theorem preserved_130 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op130 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op130 (types base) ops := @PV_B2_E_GammaOriginal.preserved_130 (types base) ops
theorem preserved_131 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op131 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op131 (types base) ops := @PV_B2_E_GammaOriginal.preserved_131 (types base) ops
theorem preserved_132 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op132 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op132 (types base) ops := @PV_B2_E_GammaOriginal.preserved_132 (types base) ops
theorem preserved_133 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op133 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op133 (types base) ops := @PV_B2_E_GammaOriginal.preserved_133 (types base) ops
theorem preserved_134 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op134 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op134 (types base) ops := @PV_B2_E_GammaOriginal.preserved_134 (types base) ops
theorem preserved_135 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op135 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op135 (types base) ops := @PV_B2_E_GammaOriginal.preserved_135 (types base) ops
theorem preserved_136 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op136 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op136 (types base) ops := @PV_B2_E_GammaOriginal.preserved_136 (types base) ops
theorem preserved_137 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op137 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op137 (types base) ops := @PV_B2_E_GammaOriginal.preserved_137 (types base) ops
theorem preserved_138 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op138 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op138 (types base) ops := @PV_B2_E_GammaOriginal.preserved_138 (types base) ops
theorem preserved_139 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op139 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op139 (types base) ops := @PV_B2_E_GammaOriginal.preserved_139 (types base) ops
theorem preserved_140 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op140 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op140 (types base) ops := @PV_B2_E_GammaOriginal.preserved_140 (types base) ops
theorem preserved_141 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op141 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op141 (types base) ops := @PV_B2_E_GammaOriginal.preserved_141 (types base) ops
theorem preserved_142 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op142 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op142 (types base) ops := @PV_B2_E_GammaOriginal.preserved_142 (types base) ops
theorem preserved_143 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op143 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op143 (types base) ops := @PV_B2_E_GammaOriginal.preserved_143 (types base) ops
theorem preserved_144 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op144 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op144 (types base) ops := @PV_B2_E_GammaOriginal.preserved_144 (types base) ops
theorem preserved_145 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op145 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op145 (types base) ops := @PV_B2_E_GammaOriginal.preserved_145 (types base) ops
theorem preserved_146 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op146 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op146 (types base) ops := @PV_B2_E_GammaOriginal.preserved_146 (types base) ops
theorem preserved_147 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op147 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op147 (types base) ops := @PV_B2_E_GammaOriginal.preserved_147 (types base) ops
theorem preserved_148 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op148 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op148 (types base) ops := @PV_B2_E_GammaOriginal.preserved_148 (types base) ops
theorem preserved_149 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op149 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op149 (types base) ops := @PV_B2_E_GammaOriginal.preserved_149 (types base) ops
theorem preserved_150 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op150 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op150 (types base) ops := @PV_B2_E_GammaOriginal.preserved_150 (types base) ops
theorem preserved_151 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op151 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op151 (types base) ops := @PV_B2_E_GammaOriginal.preserved_151 (types base) ops
theorem preserved_152 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op152 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op152 (types base) ops := @PV_B2_E_GammaOriginal.preserved_152 (types base) ops
theorem preserved_153 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op153 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op153 (types base) ops := @PV_B2_E_GammaOriginal.preserved_153 (types base) ops
theorem preserved_154 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op154 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op154 (types base) ops := @PV_B2_E_GammaOriginal.preserved_154 (types base) ops
theorem preserved_155 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op155 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op155 (types base) ops := @PV_B2_E_GammaOriginal.preserved_155 (types base) ops
theorem preserved_156 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op156 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op156 (types base) ops := @PV_B2_E_GammaOriginal.preserved_156 (types base) ops
theorem preserved_157 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op157 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op157 (types base) ops := @PV_B2_E_GammaOriginal.preserved_157 (types base) ops
theorem preserved_158 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op158 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op158 (types base) ops := @PV_B2_E_GammaOriginal.preserved_158 (types base) ops
theorem preserved_159 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op159 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op159 (types base) ops := @PV_B2_E_GammaOriginal.preserved_159 (types base) ops
theorem preserved_160 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op160 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op160 (types base) ops := @PV_B2_E_GammaOriginal.preserved_160 (types base) ops
theorem preserved_161 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op161 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op161 (types base) ops := @PV_B2_E_GammaOriginal.preserved_161 (types base) ops
theorem preserved_162 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op162 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op162 (types base) ops := @PV_B2_E_GammaOriginal.preserved_162 (types base) ops
theorem preserved_163 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op163 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op163 (types base) ops := @PV_B2_E_GammaOriginal.preserved_163 (types base) ops
theorem preserved_164 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op164 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op164 (types base) ops := @PV_B2_E_GammaOriginal.preserved_164 (types base) ops
theorem preserved_165 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op165 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op165 (types base) ops := @PV_B2_E_GammaOriginal.preserved_165 (types base) ops
theorem preserved_166 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op166 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op166 (types base) ops := @PV_B2_E_GammaOriginal.preserved_166 (types base) ops
theorem preserved_167 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op167 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op167 (types base) ops := @PV_B2_E_GammaOriginal.preserved_167 (types base) ops
theorem preserved_168 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op168 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op168 (types base) ops := @PV_B2_E_GammaOriginal.preserved_168 (types base) ops
theorem preserved_169 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op169 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op169 (types base) ops := @PV_B2_E_GammaOriginal.preserved_169 (types base) ops
theorem preserved_170 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op170 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op170 (types base) ops := @PV_B2_E_GammaOriginal.preserved_170 (types base) ops
theorem preserved_171 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op171 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op171 (types base) ops := @PV_B2_E_GammaOriginal.preserved_171 (types base) ops
theorem preserved_172 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op172 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op172 (types base) ops := @PV_B2_E_GammaOriginal.preserved_172 (types base) ops
theorem preserved_173 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op173 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op173 (types base) ops := @PV_B2_E_GammaOriginal.preserved_173 (types base) ops
theorem preserved_174 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op174 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op174 (types base) ops := @PV_B2_E_GammaOriginal.preserved_174 (types base) ops
theorem preserved_175 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op175 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op175 (types base) ops := @PV_B2_E_GammaOriginal.preserved_175 (types base) ops
theorem preserved_176 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op176 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op176 (types base) ops := @PV_B2_E_GammaOriginal.preserved_176 (types base) ops
theorem preserved_177 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op177 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op177 (types base) ops := @PV_B2_E_GammaOriginal.preserved_177 (types base) ops
theorem preserved_178 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op178 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op178 (types base) ops := @PV_B2_E_GammaOriginal.preserved_178 (types base) ops
theorem preserved_179 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op179 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op179 (types base) ops := @PV_B2_E_GammaOriginal.preserved_179 (types base) ops
theorem preserved_180 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op180 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op180 (types base) ops := @PV_B2_E_GammaOriginal.preserved_180 (types base) ops
theorem preserved_181 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op181 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op181 (types base) ops := @PV_B2_E_GammaOriginal.preserved_181 (types base) ops
theorem preserved_182 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op182 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op182 (types base) ops := @PV_B2_E_GammaOriginal.preserved_182 (types base) ops
theorem preserved_183 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op183 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op183 (types base) ops := @PV_B2_E_GammaOriginal.preserved_183 (types base) ops
theorem preserved_184 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op184 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op184 (types base) ops := @PV_B2_E_GammaOriginal.preserved_184 (types base) ops
theorem preserved_185 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op185 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op185 (types base) ops := @PV_B2_E_GammaOriginal.preserved_185 (types base) ops
theorem preserved_186 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op186 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op186 (types base) ops := @PV_B2_E_GammaOriginal.preserved_186 (types base) ops
theorem preserved_187 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op187 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op187 (types base) ops := @PV_B2_E_GammaOriginal.preserved_187 (types base) ops
theorem preserved_188 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op188 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op188 (types base) ops := @PV_B2_E_GammaOriginal.preserved_188 (types base) ops
theorem preserved_189 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op189 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op189 (types base) ops := @PV_B2_E_GammaOriginal.preserved_189 (types base) ops
theorem preserved_190 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op190 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op190 (types base) ops := @PV_B2_E_GammaOriginal.preserved_190 (types base) ops
theorem preserved_191 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op191 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op191 (types base) ops := @PV_B2_E_GammaOriginal.preserved_191 (types base) ops
theorem preserved_192 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op192 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op192 (types base) ops := @PV_B2_E_GammaOriginal.preserved_192 (types base) ops
theorem preserved_193 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op193 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op193 (types base) ops := @PV_B2_E_GammaOriginal.preserved_193 (types base) ops
theorem preserved_194 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op194 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op194 (types base) ops := @PV_B2_E_GammaOriginal.preserved_194 (types base) ops
theorem preserved_195 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op195 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op195 (types base) ops := @PV_B2_E_GammaOriginal.preserved_195 (types base) ops
theorem preserved_196 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op196 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op196 (types base) ops := @PV_B2_E_GammaOriginal.preserved_196 (types base) ops
theorem preserved_197 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op197 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op197 (types base) ops := @PV_B2_E_GammaOriginal.preserved_197 (types base) ops
theorem preserved_198 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op198 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op198 (types base) ops := @PV_B2_E_GammaOriginal.preserved_198 (types base) ops
theorem preserved_199 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op199 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op199 (types base) ops := @PV_B2_E_GammaOriginal.preserved_199 (types base) ops
theorem preserved_200 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op200 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op200 (types base) ops := @PV_B2_E_GammaOriginal.preserved_200 (types base) ops
theorem preserved_201 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op201 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op201 (types base) ops := @PV_B2_E_GammaOriginal.preserved_201 (types base) ops
theorem preserved_202 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op202 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op202 (types base) ops := @PV_B2_E_GammaOriginal.preserved_202 (types base) ops
theorem preserved_203 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op203 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op203 (types base) ops := @PV_B2_E_GammaOriginal.preserved_203 (types base) ops
theorem preserved_204 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op204 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op204 (types base) ops := @PV_B2_E_GammaOriginal.preserved_204 (types base) ops
theorem preserved_205 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op205 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op205 (types base) ops := @PV_B2_E_GammaOriginal.preserved_205 (types base) ops
theorem preserved_206 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op206 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op206 (types base) ops := @PV_B2_E_GammaOriginal.preserved_206 (types base) ops
theorem preserved_207 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op207 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op207 (types base) ops := @PV_B2_E_GammaOriginal.preserved_207 (types base) ops
theorem preserved_208 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op208 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op208 (types base) ops := @PV_B2_E_GammaOriginal.preserved_208 (types base) ops
theorem preserved_209 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op209 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op209 (types base) ops := @PV_B2_E_GammaOriginal.preserved_209 (types base) ops
theorem preserved_210 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op210 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op210 (types base) ops := @PV_B2_E_GammaOriginal.preserved_210 (types base) ops
theorem preserved_211 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op211 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op211 (types base) ops := @PV_B2_E_GammaOriginal.preserved_211 (types base) ops
theorem preserved_212 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op212 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op212 (types base) ops := @PV_B2_E_GammaOriginal.preserved_212 (types base) ops
theorem preserved_213 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op213 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op213 (types base) ops := @PV_B2_E_GammaOriginal.preserved_213 (types base) ops
theorem preserved_214 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op214 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op214 (types base) ops := @PV_B2_E_GammaOriginal.preserved_214 (types base) ops
theorem preserved_215 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op215 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op215 (types base) ops := @PV_B2_E_GammaOriginal.preserved_215 (types base) ops
theorem preserved_216 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op216 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op216 (types base) ops := @PV_B2_E_GammaOriginal.preserved_216 (types base) ops
theorem preserved_217 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op217 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op217 (types base) ops := @PV_B2_E_GammaOriginal.preserved_217 (types base) ops
theorem preserved_218 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op218 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op218 (types base) ops := @PV_B2_E_GammaOriginal.preserved_218 (types base) ops
theorem preserved_219 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op219 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op219 (types base) ops := @PV_B2_E_GammaOriginal.preserved_219 (types base) ops
theorem preserved_220 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op220 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op220 (types base) ops := @PV_B2_E_GammaOriginal.preserved_220 (types base) ops
theorem preserved_221 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op221 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op221 (types base) ops := @PV_B2_E_GammaOriginal.preserved_221 (types base) ops
theorem preserved_222 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op222 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op222 (types base) ops := @PV_B2_E_GammaOriginal.preserved_222 (types base) ops
theorem preserved_223 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op223 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op223 (types base) ops := @PV_B2_E_GammaOriginal.preserved_223 (types base) ops
theorem preserved_224 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op224 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op224 (types base) ops := @PV_B2_E_GammaOriginal.preserved_224 (types base) ops
theorem preserved_225 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op225 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op225 (types base) ops := @PV_B2_E_GammaOriginal.preserved_225 (types base) ops
theorem preserved_226 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op226 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op226 (types base) ops := @PV_B2_E_GammaOriginal.preserved_226 (types base) ops
theorem preserved_227 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op227 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op227 (types base) ops := @PV_B2_E_GammaOriginal.preserved_227 (types base) ops
theorem preserved_228 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op228 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op228 (types base) ops := @PV_B2_E_GammaOriginal.preserved_228 (types base) ops
theorem preserved_229 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op229 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op229 (types base) ops := @PV_B2_E_GammaOriginal.preserved_229 (types base) ops
theorem preserved_230 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op230 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op230 (types base) ops := @PV_B2_E_GammaOriginal.preserved_230 (types base) ops
theorem preserved_231 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op231 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op231 (types base) ops := @PV_B2_E_GammaOriginal.preserved_231 (types base) ops
theorem preserved_232 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op232 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op232 (types base) ops := @PV_B2_E_GammaOriginal.preserved_232 (types base) ops
theorem preserved_233 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op233 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op233 (types base) ops := @PV_B2_E_GammaOriginal.preserved_233 (types base) ops
theorem preserved_234 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op234 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op234 (types base) ops := @PV_B2_E_GammaOriginal.preserved_234 (types base) ops
theorem preserved_235 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op235 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op235 (types base) ops := @PV_B2_E_GammaOriginal.preserved_235 (types base) ops
theorem preserved_236 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op236 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op236 (types base) ops := @PV_B2_E_GammaOriginal.preserved_236 (types base) ops
theorem preserved_237 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op237 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op237 (types base) ops := @PV_B2_E_GammaOriginal.preserved_237 (types base) ops
theorem preserved_238 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op238 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op238 (types base) ops := @PV_B2_E_GammaOriginal.preserved_238 (types base) ops
theorem preserved_239 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op239 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op239 (types base) ops := @PV_B2_E_GammaOriginal.preserved_239 (types base) ops
theorem preserved_240 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op240 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op240 (types base) ops := @PV_B2_E_GammaOriginal.preserved_240 (types base) ops
theorem preserved_241 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op241 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op241 (types base) ops := @PV_B2_E_GammaOriginal.preserved_241 (types base) ops
theorem preserved_242 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op242 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op242 (types base) ops := @PV_B2_E_GammaOriginal.preserved_242 (types base) ops
theorem preserved_243 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op243 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op243 (types base) ops := @PV_B2_E_GammaOriginal.preserved_243 (types base) ops
theorem preserved_244 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op244 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op244 (types base) ops := @PV_B2_E_GammaOriginal.preserved_244 (types base) ops
theorem preserved_245 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op245 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op245 (types base) ops := @PV_B2_E_GammaOriginal.preserved_245 (types base) ops
theorem preserved_246 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op246 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op246 (types base) ops := @PV_B2_E_GammaOriginal.preserved_246 (types base) ops
theorem preserved_247 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op247 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op247 (types base) ops := @PV_B2_E_GammaOriginal.preserved_247 (types base) ops
theorem preserved_248 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op248 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op248 (types base) ops := @PV_B2_E_GammaOriginal.preserved_248 (types base) ops
theorem preserved_252 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op252 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op252 (types base) ops := @PV_B2_E_GammaOriginal.preserved_252 (types base) ops
theorem preserved_253 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op253 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op253 (types base) ops := @PV_B2_E_GammaOriginal.preserved_253 (types base) ops
theorem preserved_254 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op254 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op254 (types base) ops := @PV_B2_E_GammaOriginal.preserved_254 (types base) ops
theorem preserved_255 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op255 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op255 (types base) ops := @PV_B2_E_GammaOriginal.preserved_255 (types base) ops
theorem preserved_256 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op256 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op256 (types base) ops := @PV_B2_E_GammaOriginal.preserved_256 (types base) ops
theorem preserved_257 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op257 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op257 (types base) ops := @PV_B2_E_GammaOriginal.preserved_257 (types base) ops
theorem preserved_258 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op258 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op258 (types base) ops := @PV_B2_E_GammaOriginal.preserved_258 (types base) ops
theorem preserved_259 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op259 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op259 (types base) ops := @PV_B2_E_GammaOriginal.preserved_259 (types base) ops
theorem preserved_260 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op260 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op260 (types base) ops := @PV_B2_E_GammaOriginal.preserved_260 (types base) ops
theorem preserved_261 (base : ProverRwFull.ExternalTypes) (event : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op261 (types base) (selected base event ops) =
      @ProverRwFull.ExternalFuns.op261 (types base) ops := @PV_B2_E_GammaOriginal.preserved_261 (types base) ops
#print axioms roundtrip
#print axioms roundtrip_native
#print axioms callbacks
#print axioms selected_callback
#print axioms nonvacuity
#print axioms allocation_error
#print axioms dictionaries
#print axioms observations
#print axioms preserved_0
#print axioms preserved_1
#print axioms preserved_2
#print axioms preserved_3
#print axioms preserved_4
#print axioms preserved_5
#print axioms preserved_6
#print axioms preserved_7
#print axioms preserved_8
#print axioms preserved_9
#print axioms preserved_10
#print axioms preserved_11
#print axioms preserved_12
#print axioms preserved_13
#print axioms preserved_14
#print axioms preserved_15
#print axioms preserved_16
#print axioms preserved_17
#print axioms preserved_18
#print axioms preserved_19
#print axioms preserved_20
#print axioms preserved_21
#print axioms preserved_22
#print axioms preserved_23
#print axioms preserved_24
#print axioms preserved_25
#print axioms preserved_26
#print axioms preserved_27
#print axioms preserved_28
#print axioms preserved_29
#print axioms preserved_30
#print axioms preserved_31
#print axioms preserved_32
#print axioms preserved_33
#print axioms preserved_34
#print axioms preserved_35
#print axioms preserved_36
#print axioms preserved_37
#print axioms preserved_38
#print axioms preserved_39
#print axioms preserved_40
#print axioms preserved_41
#print axioms preserved_42
#print axioms preserved_43
#print axioms preserved_44
#print axioms preserved_45
#print axioms preserved_46
#print axioms preserved_47
#print axioms preserved_48
#print axioms preserved_49
#print axioms preserved_50
#print axioms preserved_51
#print axioms preserved_52
#print axioms preserved_53
#print axioms preserved_54
#print axioms preserved_55
#print axioms preserved_56
#print axioms preserved_57
#print axioms preserved_58
#print axioms preserved_59
#print axioms preserved_60
#print axioms preserved_61
#print axioms preserved_62
#print axioms preserved_63
#print axioms preserved_64
#print axioms preserved_65
#print axioms preserved_66
#print axioms preserved_67
#print axioms preserved_68
#print axioms preserved_69
#print axioms preserved_70
#print axioms preserved_71
#print axioms preserved_72
#print axioms preserved_73
#print axioms preserved_74
#print axioms preserved_75
#print axioms preserved_76
#print axioms preserved_77
#print axioms preserved_78
#print axioms preserved_79
#print axioms preserved_80
#print axioms preserved_81
#print axioms preserved_82
#print axioms preserved_83
#print axioms preserved_84
#print axioms preserved_85
#print axioms preserved_86
#print axioms preserved_87
#print axioms preserved_88
#print axioms preserved_89
#print axioms preserved_90
#print axioms preserved_91
#print axioms preserved_92
#print axioms preserved_93
#print axioms preserved_94
#print axioms preserved_95
#print axioms preserved_96
#print axioms preserved_97
#print axioms preserved_98
#print axioms preserved_99
#print axioms preserved_100
#print axioms preserved_101
#print axioms preserved_102
#print axioms preserved_103
#print axioms preserved_104
#print axioms preserved_105
#print axioms preserved_106
#print axioms preserved_107
#print axioms preserved_108
#print axioms preserved_109
#print axioms preserved_110
#print axioms preserved_111
#print axioms preserved_112
#print axioms preserved_113
#print axioms preserved_114
#print axioms preserved_115
#print axioms preserved_116
#print axioms preserved_117
#print axioms preserved_118
#print axioms preserved_119
#print axioms preserved_120
#print axioms preserved_121
#print axioms preserved_122
#print axioms preserved_123
#print axioms preserved_124
#print axioms preserved_125
#print axioms preserved_126
#print axioms preserved_127
#print axioms preserved_128
#print axioms preserved_129
#print axioms preserved_130
#print axioms preserved_131
#print axioms preserved_132
#print axioms preserved_133
#print axioms preserved_134
#print axioms preserved_135
#print axioms preserved_136
#print axioms preserved_137
#print axioms preserved_138
#print axioms preserved_139
#print axioms preserved_140
#print axioms preserved_141
#print axioms preserved_142
#print axioms preserved_143
#print axioms preserved_144
#print axioms preserved_145
#print axioms preserved_146
#print axioms preserved_147
#print axioms preserved_148
#print axioms preserved_149
#print axioms preserved_150
#print axioms preserved_151
#print axioms preserved_152
#print axioms preserved_153
#print axioms preserved_154
#print axioms preserved_155
#print axioms preserved_156
#print axioms preserved_157
#print axioms preserved_158
#print axioms preserved_159
#print axioms preserved_160
#print axioms preserved_161
#print axioms preserved_162
#print axioms preserved_163
#print axioms preserved_164
#print axioms preserved_165
#print axioms preserved_166
#print axioms preserved_167
#print axioms preserved_168
#print axioms preserved_169
#print axioms preserved_170
#print axioms preserved_171
#print axioms preserved_172
#print axioms preserved_173
#print axioms preserved_174
#print axioms preserved_175
#print axioms preserved_176
#print axioms preserved_177
#print axioms preserved_178
#print axioms preserved_179
#print axioms preserved_180
#print axioms preserved_181
#print axioms preserved_182
#print axioms preserved_183
#print axioms preserved_184
#print axioms preserved_185
#print axioms preserved_186
#print axioms preserved_187
#print axioms preserved_188
#print axioms preserved_189
#print axioms preserved_190
#print axioms preserved_191
#print axioms preserved_192
#print axioms preserved_193
#print axioms preserved_194
#print axioms preserved_195
#print axioms preserved_196
#print axioms preserved_197
#print axioms preserved_198
#print axioms preserved_199
#print axioms preserved_200
#print axioms preserved_201
#print axioms preserved_202
#print axioms preserved_203
#print axioms preserved_204
#print axioms preserved_205
#print axioms preserved_206
#print axioms preserved_207
#print axioms preserved_208
#print axioms preserved_209
#print axioms preserved_210
#print axioms preserved_211
#print axioms preserved_212
#print axioms preserved_213
#print axioms preserved_214
#print axioms preserved_215
#print axioms preserved_216
#print axioms preserved_217
#print axioms preserved_218
#print axioms preserved_219
#print axioms preserved_220
#print axioms preserved_221
#print axioms preserved_222
#print axioms preserved_223
#print axioms preserved_224
#print axioms preserved_225
#print axioms preserved_226
#print axioms preserved_227
#print axioms preserved_228
#print axioms preserved_229
#print axioms preserved_230
#print axioms preserved_231
#print axioms preserved_232
#print axioms preserved_233
#print axioms preserved_234
#print axioms preserved_235
#print axioms preserved_236
#print axioms preserved_237
#print axioms preserved_238
#print axioms preserved_239
#print axioms preserved_240
#print axioms preserved_241
#print axioms preserved_242
#print axioms preserved_243
#print axioms preserved_244
#print axioms preserved_245
#print axioms preserved_246
#print axioms preserved_247
#print axioms preserved_248
#print axioms preserved_252
#print axioms preserved_253
#print axioms preserved_254
#print axioms preserved_255
#print axioms preserved_256
#print axioms preserved_257
#print axioms preserved_258
#print axioms preserved_259
#print axioms preserved_260
#print axioms preserved_261
end PV_B2_F_MaterializeNative

end
end

section
-- Unchanged source component: R1Z.PV_B2_F_251Bridge
set_option autoImplicit false
noncomputable section
namespace PV_B2_F_251Bridge
open Aeneas Aeneas.Std Result
open PV_B2_F_MaterializeNative
/-- Exact selected callback on the native carrier, full Result, every raw weight,
kappa, and allocation request result. This is not the native execution join. -/
theorem source (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) (w : W) (kappa : Native) :
    @ProverRwFull.ExternalFuns.op251 (types base) (selected base request ops) w kappa =
      PV_B2_E_OrdinaryOriginal.mapResult mapRust
        (PV_B2_F_MaterializeRequest.original request w (fromNative kappa)) := by
  change PV_B2_E_OrdinaryOriginal.mapResult mapRust
    (PV_B2_F_AllocationEffects.copied request w (fromNative kappa)) = _
  rw [PV_B2_F_MaterializeRequest.complete_result]

theorem nonvacuity (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (types base)) (w : W) (kappa : Native) :
    ∃ out, @ProverRwFull.ExternalFuns.op251 (types base)
      (selected base (ok .supplied) ops) w kappa = ok (.Ok out) :=
  PV_B2_F_MaterializeNative.nonvacuity base ops w kappa

theorem allocation_error (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (types base)) (w : W) (kappa : Native) :
    @ProverRwFull.ExternalFuns.op251 (types base)
      (selected base (ok .denied) ops) w kappa = ok (.Err ProverRwFull.verifier.Error.Allocation) :=
  PV_B2_F_MaterializeNative.allocation_error base ops w kappa

theorem failure (base : ProverRwFull.ExternalTypes) (e : Error)
    (ops : @ProverRwFull.ExternalFuns (types base)) (w : W) (kappa : Native) :
    @ProverRwFull.ExternalFuns.op251 (types base)
      (selected base (fail e) ops) w kappa = fail e := rfl

theorem divergence (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (types base)) (w : W) (kappa : Native) :
    @ProverRwFull.ExternalFuns.op251 (types base)
      (selected base div ops) w kappa = div := rfl

theorem gamma_preserved (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op249 (types base) (selected base request ops) =
      @ProverRwFull.ExternalFuns.op249 (types base)
        (@PV_B2_E_GammaOriginal.selected (types base) ops) := rfl

theorem ordinary_preserved (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op250 (types base) (selected base request ops) =
      @ProverRwFull.ExternalFuns.op250 (types base)
        (@PV_B2_E_GammaOriginal.selected (types base) ops) := rfl
#print axioms source
#print axioms nonvacuity
#print axioms allocation_error
#print axioms failure
#print axioms divergence
#print axioms gamma_preserved
#print axioms ordinary_preserved
end PV_B2_F_251Bridge

end
end

section
-- Unchanged source component: R1Z.PV_B2_F_ConstructorCarrier
set_option autoImplicit false
namespace PV_B2_F_ConstructorCarrier
open Aeneas Aeneas.Std Result
abbrev K := PV_B2_C_Carrier.aspis_core.field.QM31
abbrev Point := PV_B2_C_Carrier.aspis_core.circle.SecureCirclePoint
abbrev Variant := PV_B2_C_Carrier.transport.Variant
abbrev Weight := PV_B2_C_WeightsNative.host_weights.Weights
abbrev W := PV_B2_F_MaterializeNative.W
abbrev NQ := ProverRwFull.aspis_core.field.QM31
abbrev NP := ProverRwFull.aspis_core.circle.SecureCirclePoint
abbrev NV := ProverRwFull.transport.Variant

def amap {α β : Type} {n : Usize} (f : α → β) (a : Array α n) : Array β n :=
  ⟨a.val.map f,by rw [List.length_map,a.property]⟩

def fromQ (q : NQ) : K := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def toQ (q : K) : NQ := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def to251Q (q : K) : PV_B2_251c1.aspis_core.field.QM31 :=
  ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def fromPoint (p : NP) : Point := ⟨fromQ p.x,fromQ p.y⟩
def toPoint (p : Point) : NP := ⟨toQ p.x,toQ p.y⟩
def fromVariant : NV → Variant
  | .S1 => .S1
  | .S2 => .S2
  | .D => .D
def toVariant : Variant → NV
  | .S1 => .S1
  | .S2 => .S2
  | .D => .D
def to251Variant : Variant → PV_B2_251c1.transport.Variant
  | .S1 => .S1
  | .S2 => .S2
  | .D => .D

def toWeight (w : Weight) : W :=
  ⟨to251Variant w.variant,amap (amap (amap to251Q)) w.factors,
   amap (amap to251Q) w.points,amap to251Q w.extra⟩

def toError : PV_B2_C_Carrier.verifier.Error → ProverRwFull.verifier.Error
  | .Parse => .Parse
  | .Semantic => .Semantic
  | .Transcript => .Transcript
  | .Relation => .Relation
  | .Merkle => .Merkle
  | .Query => .Query
  | .Checkpoint => .Checkpoint
  | .Allocation => .Allocation
  | .Rejected => .Rejected
  | .AttemptsExhausted => .AttemptsExhausted
  | .Entropy => .Entropy

theorem q_roundtrip (q : NQ) : toQ (fromQ q)=q := by cases q; rfl
theorem q_roundtrip_kernel (q : K) : fromQ (toQ q)=q := by cases q; rfl
theorem point_roundtrip (p : NP) : toPoint (fromPoint p)=p := by cases p; rfl
theorem variant_roundtrip (v : NV) : toVariant (fromVariant v)=v := by cases v <;> rfl

theorem weight_factors (w : Weight) :
    (toWeight w).factors = amap (amap (amap to251Q)) w.factors := rfl
theorem weight_points (w : Weight) :
    (toWeight w).points = amap (amap to251Q) w.points := rfl
theorem weight_extra (w : Weight) : (toWeight w).extra = amap to251Q w.extra := rfl
#print axioms q_roundtrip
#print axioms q_roundtrip_kernel
#print axioms point_roundtrip
#print axioms variant_roundtrip
#print axioms weight_factors
#print axioms weight_points
#print axioms weight_extra
end PV_B2_F_ConstructorCarrier

end

section
-- Unchanged source component: R1Z.PV_B2_F_ConstructorCarrierLaws
set_option autoImplicit false
namespace PV_B2_F_ConstructorCarrierLaws
open Aeneas Aeneas.Std Result PV_B2_F_ConstructorCarrier

theorem amap_roundtrip {α β : Type} {n : Usize} (f : α → β) (g : β → α)
    (h : ∀ x,g (f x)=x) (a : Array α n) : amap g (amap f a)=a := by
  apply Subtype.ext
  change (a.val.map f).map g = a.val
  simp [List.map_map,Function.comp_def,h]

def from251Q (q : PV_B2_251c1.aspis_core.field.QM31) : K :=
  ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def from251Variant : PV_B2_251c1.transport.Variant → Variant
  | .S1 => .S1
  | .S2 => .S2
  | .D => .D

theorem q_roundtrip (q : K) : from251Q (to251Q q)=q := by cases q; rfl
theorem variant_roundtrip (v : Variant) : from251Variant (to251Variant v)=v := by cases v <;> rfl

theorem q_array_roundtrip {n : Usize} (a : Array K n) :
    amap from251Q (amap to251Q a)=a := amap_roundtrip _ _ q_roundtrip a

theorem q_matrix_roundtrip {n m : Usize} (a : Array (Array K n) m) :
    amap (amap from251Q) (amap (amap to251Q) a)=a :=
  amap_roundtrip _ _ q_array_roundtrip a

theorem q_tensor_roundtrip {n m k : Usize} (a : Array (Array (Array K n) m) k) :
    amap (amap (amap from251Q)) (amap (amap (amap to251Q)) a)=a :=
  amap_roundtrip _ _ q_matrix_roundtrip a

def fromWeight (w : W) : Weight :=
  ⟨from251Variant w.variant,amap (amap (amap from251Q)) w.factors,
   amap (amap from251Q) w.points,amap from251Q w.extra⟩

theorem weight_roundtrip (w : Weight) : fromWeight (toWeight w)=w := by
  rcases w with ⟨v,f,p,e⟩
  simp only [fromWeight,toWeight,variant_roundtrip,q_tensor_roundtrip,q_matrix_roundtrip,q_array_roundtrip]

theorem alpha_roundtrip (alpha : Array NQ 10#usize) : amap toQ (amap fromQ alpha)=alpha :=
  amap_roundtrip _ _ PV_B2_F_ConstructorCarrier.q_roundtrip alpha

theorem points_roundtrip (z : Array NP 2#usize) : amap toPoint (amap fromPoint z)=z :=
  amap_roundtrip _ _ PV_B2_F_ConstructorCarrier.point_roundtrip z
#print axioms amap_roundtrip
#print axioms q_roundtrip
#print axioms variant_roundtrip
#print axioms q_array_roundtrip
#print axioms q_matrix_roundtrip
#print axioms q_tensor_roundtrip
#print axioms weight_roundtrip
#print axioms alpha_roundtrip
#print axioms points_roundtrip
end PV_B2_F_ConstructorCarrierLaws

end

section
-- Unchanged source component: R1Z.PV_B2_F_ConstructorEffect
set_option autoImplicit false
namespace PV_B2_F_ConstructorEffect
open Aeneas Aeneas.Std Result PV_B2_F_ConstructorCarrier
abbrev RustResult := core.result.Result W ProverRwFull.verifier.Error
/-- Box::new is retained at the actual prover caller. An allocation abort is an
outer failure, not a fabricated Rust Error::Allocation return. -/
def finish (boxRequest : Result Unit)
    (r : core.result.Result Weight PV_B2_C_Carrier.verifier.Error) : Result RustResult :=
  match r with
  | .Err e => ok (.Err (toError e))
  | .Ok w => do
    let _ ← boxRequest
    ok (.Ok (toWeight w))

def copied (boxRequest : Result Unit) (v : NV) (alpha : Array NQ 10#usize)
    (z : Array NP 2#usize) : Result RustResult := do
  let r ← PV_B2_C_WeightsNative.host_weights.Weights.new (fromVariant v)
    (amap fromQ alpha) (amap fromPoint z)
  finish boxRequest r

def original (boxRequest : Result Unit) (v : NV) (alpha : Array NQ 10#usize)
    (z : Array NP 2#usize) : Result RustResult := do
  let r ← PV_B2_C_ConstructorSuccess.staged (fromVariant v)
    (amap fromQ alpha) (amap fromPoint z)
  finish boxRequest r

/-- All raw inputs and every Box request Result. No input validity, constructor
success or native allocation-success hypothesis is supplied by the caller. -/
theorem complete_result (boxRequest : Result Unit) (v : NV) (alpha : Array NQ 10#usize)
    (z : Array NP 2#usize) : copied boxRequest v alpha z = original boxRequest v alpha z := by
  unfold copied original
  rw [PV_B2_C_ConstructorSuccess.new_eq_staged]

theorem value_law (v : NV) (alpha : Array NQ 10#usize) (z : Array NP 2#usize) :
    ∃ w : Weight,
      PV_B2_C_WeightsNative.host_weights.Weights.new (fromVariant v)
        (amap fromQ alpha) (amap fromPoint z) = ok (.Ok w) ∧
      copied (ok ()) v alpha z = ok (.Ok (toWeight w)) := by
  obtain ⟨w,hw⟩ := PV_B2_C_ConstructorSuccess.new_total (fromVariant v)
    (amap fromQ alpha) (amap fromPoint z)
  exact ⟨w,hw,by simp only [copied,hw,bind_tc_ok,finish]⟩

theorem failure (e : Error) (v : NV) (alpha : Array NQ 10#usize) (z : Array NP 2#usize) :
    copied (fail e) v alpha z = fail e := by
  obtain ⟨w,hw⟩ := PV_B2_C_ConstructorSuccess.new_total (fromVariant v)
    (amap fromQ alpha) (amap fromPoint z)
  simp only [copied,hw,bind_tc_ok,finish,bind_tc_fail]

theorem divergence (v : NV) (alpha : Array NQ 10#usize) (z : Array NP 2#usize) :
    copied div v alpha z = div := by
  obtain ⟨w,hw⟩ := PV_B2_C_ConstructorSuccess.new_total (fromVariant v)
    (amap fromQ alpha) (amap fromPoint z)
  simp only [copied,hw,bind_tc_ok,finish,bind_tc_div]

theorem rust_error (boxRequest : Result Unit) (e : PV_B2_C_Carrier.verifier.Error) :
    finish boxRequest (.Err e) = ok (.Err (toError e)) := rfl
#print axioms complete_result
#print axioms value_law
#print axioms failure
#print axioms divergence
#print axioms rust_error
end PV_B2_F_ConstructorEffect

end

section
-- Unchanged source component: R1Z.PV_B2_F_ConstructorNative
set_option autoImplicit false
noncomputable section
namespace PV_B2_F_ConstructorNative
open Aeneas Aeneas.Std Result PV_B2_F_ConstructorCarrier
abbrev types := PV_B2_F_MaterializeNative.types
abbrev Outcome := PV_B2_F_MaterializeNative.Outcome

def selected (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns (types base) :=
  letI : ProverRwFull.ExternalTypes := types base
  {PV_B2_F_MaterializeNative.selected base request ops with op252 := PV_B2_F_ConstructorEffect.copied boxRequest}

def originalDictionary (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns (types base) :=
  letI : ProverRwFull.ExternalTypes := types base
  {PV_B2_F_MaterializeNative.originalDictionary base request ops with op252 := PV_B2_F_ConstructorEffect.original boxRequest}

theorem source (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base))
    (v : NV) (alpha : Array NQ 10#usize) (z : Array NP 2#usize) :
    @ProverRwFull.ExternalFuns.op252 (types base) (selected base request boxRequest ops) v alpha z =
      PV_B2_F_ConstructorEffect.original boxRequest v alpha z :=
  PV_B2_F_ConstructorEffect.complete_result boxRequest v alpha z

theorem value_law (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base))
    (v : NV) (alpha : Array NQ 10#usize) (z : Array NP 2#usize) :
    ∃ w : Weight,
      PV_B2_C_WeightsNative.host_weights.Weights.new (fromVariant v)
        (amap fromQ alpha) (amap fromPoint z) = ok (.Ok w) ∧
      @ProverRwFull.ExternalFuns.op252 (types base) (selected base request (ok ()) ops) v alpha z =
        ok (.Ok (toWeight w)) := PV_B2_F_ConstructorEffect.value_law v alpha z

theorem nonvacuity (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base))
    (v : NV) (alpha : Array NQ 10#usize) (z : Array NP 2#usize) :
    ∃ w, @ProverRwFull.ExternalFuns.op252 (types base) (selected base request (ok ()) ops) v alpha z =
      ok (.Ok w) := by
  obtain ⟨w,_,hw⟩ := value_law base request ops v alpha z
  exact ⟨toWeight w,hw⟩

theorem failure (base : ProverRwFull.ExternalTypes) (request : Result Outcome) (e : Error)
    (ops : @ProverRwFull.ExternalFuns (types base))
    (v : NV) (alpha : Array NQ 10#usize) (z : Array NP 2#usize) :
    @ProverRwFull.ExternalFuns.op252 (types base) (selected base request (fail e) ops) v alpha z = fail e :=
  PV_B2_F_ConstructorEffect.failure e v alpha z

theorem divergence (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base))
    (v : NV) (alpha : Array NQ 10#usize) (z : Array NP 2#usize) :
    @ProverRwFull.ExternalFuns.op252 (types base) (selected base request div ops) v alpha z = div :=
  PV_B2_F_ConstructorEffect.divergence v alpha z

theorem dictionaries (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    selected base request boxRequest ops = originalDictionary base request boxRequest ops := by
  have hc : PV_B2_F_ConstructorEffect.copied boxRequest = PV_B2_F_ConstructorEffect.original boxRequest := by
    funext v alpha z
    exact PV_B2_F_ConstructorEffect.complete_result boxRequest v alpha z
  unfold selected originalDictionary
  rw [PV_B2_F_MaterializeNative.dictionaries,hc]

theorem observations {O : Sort _} (base : ProverRwFull.ExternalTypes)
    (observe : @ProverRwFull.ExternalFuns (types base) → O) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    observe (selected base request boxRequest ops) = observe (originalDictionary base request boxRequest ops) :=
  congrArg observe (dictionaries base request boxRequest ops)
theorem preserved_0 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op0 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op0 (types base) ops := PV_B2_F_MaterializeNative.preserved_0 base request ops
theorem preserved_1 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op1 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op1 (types base) ops := PV_B2_F_MaterializeNative.preserved_1 base request ops
theorem preserved_2 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op2 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op2 (types base) ops := PV_B2_F_MaterializeNative.preserved_2 base request ops
theorem preserved_3 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op3 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op3 (types base) ops := PV_B2_F_MaterializeNative.preserved_3 base request ops
theorem preserved_4 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op4 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op4 (types base) ops := PV_B2_F_MaterializeNative.preserved_4 base request ops
theorem preserved_5 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op5 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op5 (types base) ops := PV_B2_F_MaterializeNative.preserved_5 base request ops
theorem preserved_6 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op6 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op6 (types base) ops := PV_B2_F_MaterializeNative.preserved_6 base request ops
theorem preserved_7 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op7 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op7 (types base) ops := PV_B2_F_MaterializeNative.preserved_7 base request ops
theorem preserved_8 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op8 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op8 (types base) ops := PV_B2_F_MaterializeNative.preserved_8 base request ops
theorem preserved_9 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op9 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op9 (types base) ops := PV_B2_F_MaterializeNative.preserved_9 base request ops
theorem preserved_10 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op10 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op10 (types base) ops := PV_B2_F_MaterializeNative.preserved_10 base request ops
theorem preserved_11 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op11 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op11 (types base) ops := PV_B2_F_MaterializeNative.preserved_11 base request ops
theorem preserved_12 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op12 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op12 (types base) ops := PV_B2_F_MaterializeNative.preserved_12 base request ops
theorem preserved_13 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op13 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op13 (types base) ops := PV_B2_F_MaterializeNative.preserved_13 base request ops
theorem preserved_14 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op14 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op14 (types base) ops := PV_B2_F_MaterializeNative.preserved_14 base request ops
theorem preserved_15 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op15 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op15 (types base) ops := PV_B2_F_MaterializeNative.preserved_15 base request ops
theorem preserved_16 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op16 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op16 (types base) ops := PV_B2_F_MaterializeNative.preserved_16 base request ops
theorem preserved_17 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op17 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op17 (types base) ops := PV_B2_F_MaterializeNative.preserved_17 base request ops
theorem preserved_18 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op18 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op18 (types base) ops := PV_B2_F_MaterializeNative.preserved_18 base request ops
theorem preserved_19 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op19 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op19 (types base) ops := PV_B2_F_MaterializeNative.preserved_19 base request ops
theorem preserved_20 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op20 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op20 (types base) ops := PV_B2_F_MaterializeNative.preserved_20 base request ops
theorem preserved_21 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op21 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op21 (types base) ops := PV_B2_F_MaterializeNative.preserved_21 base request ops
theorem preserved_22 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op22 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op22 (types base) ops := PV_B2_F_MaterializeNative.preserved_22 base request ops
theorem preserved_23 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op23 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op23 (types base) ops := PV_B2_F_MaterializeNative.preserved_23 base request ops
theorem preserved_24 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op24 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op24 (types base) ops := PV_B2_F_MaterializeNative.preserved_24 base request ops
theorem preserved_25 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op25 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op25 (types base) ops := PV_B2_F_MaterializeNative.preserved_25 base request ops
theorem preserved_26 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op26 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op26 (types base) ops := PV_B2_F_MaterializeNative.preserved_26 base request ops
theorem preserved_27 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op27 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op27 (types base) ops := PV_B2_F_MaterializeNative.preserved_27 base request ops
theorem preserved_28 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op28 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op28 (types base) ops := PV_B2_F_MaterializeNative.preserved_28 base request ops
theorem preserved_29 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op29 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op29 (types base) ops := PV_B2_F_MaterializeNative.preserved_29 base request ops
theorem preserved_30 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op30 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op30 (types base) ops := PV_B2_F_MaterializeNative.preserved_30 base request ops
theorem preserved_31 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op31 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op31 (types base) ops := PV_B2_F_MaterializeNative.preserved_31 base request ops
theorem preserved_32 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op32 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op32 (types base) ops := PV_B2_F_MaterializeNative.preserved_32 base request ops
theorem preserved_33 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op33 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op33 (types base) ops := PV_B2_F_MaterializeNative.preserved_33 base request ops
theorem preserved_34 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op34 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op34 (types base) ops := PV_B2_F_MaterializeNative.preserved_34 base request ops
theorem preserved_35 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op35 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op35 (types base) ops := PV_B2_F_MaterializeNative.preserved_35 base request ops
theorem preserved_36 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op36 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op36 (types base) ops := PV_B2_F_MaterializeNative.preserved_36 base request ops
theorem preserved_37 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op37 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op37 (types base) ops := PV_B2_F_MaterializeNative.preserved_37 base request ops
theorem preserved_38 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op38 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op38 (types base) ops := PV_B2_F_MaterializeNative.preserved_38 base request ops
theorem preserved_39 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op39 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op39 (types base) ops := PV_B2_F_MaterializeNative.preserved_39 base request ops
theorem preserved_40 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op40 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op40 (types base) ops := PV_B2_F_MaterializeNative.preserved_40 base request ops
theorem preserved_41 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op41 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op41 (types base) ops := PV_B2_F_MaterializeNative.preserved_41 base request ops
theorem preserved_42 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op42 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op42 (types base) ops := PV_B2_F_MaterializeNative.preserved_42 base request ops
theorem preserved_43 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op43 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op43 (types base) ops := PV_B2_F_MaterializeNative.preserved_43 base request ops
theorem preserved_44 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op44 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op44 (types base) ops := PV_B2_F_MaterializeNative.preserved_44 base request ops
theorem preserved_45 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op45 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op45 (types base) ops := PV_B2_F_MaterializeNative.preserved_45 base request ops
theorem preserved_46 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op46 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op46 (types base) ops := PV_B2_F_MaterializeNative.preserved_46 base request ops
theorem preserved_47 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op47 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op47 (types base) ops := PV_B2_F_MaterializeNative.preserved_47 base request ops
theorem preserved_48 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op48 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op48 (types base) ops := PV_B2_F_MaterializeNative.preserved_48 base request ops
theorem preserved_49 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op49 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op49 (types base) ops := PV_B2_F_MaterializeNative.preserved_49 base request ops
theorem preserved_50 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op50 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op50 (types base) ops := PV_B2_F_MaterializeNative.preserved_50 base request ops
theorem preserved_51 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op51 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op51 (types base) ops := PV_B2_F_MaterializeNative.preserved_51 base request ops
theorem preserved_52 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op52 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op52 (types base) ops := PV_B2_F_MaterializeNative.preserved_52 base request ops
theorem preserved_53 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op53 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op53 (types base) ops := PV_B2_F_MaterializeNative.preserved_53 base request ops
theorem preserved_54 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op54 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op54 (types base) ops := PV_B2_F_MaterializeNative.preserved_54 base request ops
theorem preserved_55 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op55 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op55 (types base) ops := PV_B2_F_MaterializeNative.preserved_55 base request ops
theorem preserved_56 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op56 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op56 (types base) ops := PV_B2_F_MaterializeNative.preserved_56 base request ops
theorem preserved_57 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op57 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op57 (types base) ops := PV_B2_F_MaterializeNative.preserved_57 base request ops
theorem preserved_58 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op58 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op58 (types base) ops := PV_B2_F_MaterializeNative.preserved_58 base request ops
theorem preserved_59 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op59 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op59 (types base) ops := PV_B2_F_MaterializeNative.preserved_59 base request ops
theorem preserved_60 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op60 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op60 (types base) ops := PV_B2_F_MaterializeNative.preserved_60 base request ops
theorem preserved_61 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op61 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op61 (types base) ops := PV_B2_F_MaterializeNative.preserved_61 base request ops
theorem preserved_62 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op62 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op62 (types base) ops := PV_B2_F_MaterializeNative.preserved_62 base request ops
theorem preserved_63 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op63 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op63 (types base) ops := PV_B2_F_MaterializeNative.preserved_63 base request ops
theorem preserved_64 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op64 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op64 (types base) ops := PV_B2_F_MaterializeNative.preserved_64 base request ops
theorem preserved_65 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op65 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op65 (types base) ops := PV_B2_F_MaterializeNative.preserved_65 base request ops
theorem preserved_66 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op66 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op66 (types base) ops := PV_B2_F_MaterializeNative.preserved_66 base request ops
theorem preserved_67 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op67 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op67 (types base) ops := PV_B2_F_MaterializeNative.preserved_67 base request ops
theorem preserved_68 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op68 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op68 (types base) ops := PV_B2_F_MaterializeNative.preserved_68 base request ops
theorem preserved_69 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op69 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op69 (types base) ops := PV_B2_F_MaterializeNative.preserved_69 base request ops
theorem preserved_70 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op70 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op70 (types base) ops := PV_B2_F_MaterializeNative.preserved_70 base request ops
theorem preserved_71 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op71 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op71 (types base) ops := PV_B2_F_MaterializeNative.preserved_71 base request ops
theorem preserved_72 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op72 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op72 (types base) ops := PV_B2_F_MaterializeNative.preserved_72 base request ops
theorem preserved_73 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op73 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op73 (types base) ops := PV_B2_F_MaterializeNative.preserved_73 base request ops
theorem preserved_74 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op74 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op74 (types base) ops := PV_B2_F_MaterializeNative.preserved_74 base request ops
theorem preserved_75 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op75 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op75 (types base) ops := PV_B2_F_MaterializeNative.preserved_75 base request ops
theorem preserved_76 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op76 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op76 (types base) ops := PV_B2_F_MaterializeNative.preserved_76 base request ops
theorem preserved_77 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op77 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op77 (types base) ops := PV_B2_F_MaterializeNative.preserved_77 base request ops
theorem preserved_78 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op78 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op78 (types base) ops := PV_B2_F_MaterializeNative.preserved_78 base request ops
theorem preserved_79 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op79 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op79 (types base) ops := PV_B2_F_MaterializeNative.preserved_79 base request ops
theorem preserved_80 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op80 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op80 (types base) ops := PV_B2_F_MaterializeNative.preserved_80 base request ops
theorem preserved_81 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op81 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op81 (types base) ops := PV_B2_F_MaterializeNative.preserved_81 base request ops
theorem preserved_82 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op82 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op82 (types base) ops := PV_B2_F_MaterializeNative.preserved_82 base request ops
theorem preserved_83 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op83 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op83 (types base) ops := PV_B2_F_MaterializeNative.preserved_83 base request ops
theorem preserved_84 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op84 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op84 (types base) ops := PV_B2_F_MaterializeNative.preserved_84 base request ops
theorem preserved_85 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op85 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op85 (types base) ops := PV_B2_F_MaterializeNative.preserved_85 base request ops
theorem preserved_86 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op86 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op86 (types base) ops := PV_B2_F_MaterializeNative.preserved_86 base request ops
theorem preserved_87 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op87 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op87 (types base) ops := PV_B2_F_MaterializeNative.preserved_87 base request ops
theorem preserved_88 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op88 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op88 (types base) ops := PV_B2_F_MaterializeNative.preserved_88 base request ops
theorem preserved_89 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op89 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op89 (types base) ops := PV_B2_F_MaterializeNative.preserved_89 base request ops
theorem preserved_90 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op90 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op90 (types base) ops := PV_B2_F_MaterializeNative.preserved_90 base request ops
theorem preserved_91 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op91 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op91 (types base) ops := PV_B2_F_MaterializeNative.preserved_91 base request ops
theorem preserved_92 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op92 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op92 (types base) ops := PV_B2_F_MaterializeNative.preserved_92 base request ops
theorem preserved_93 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op93 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op93 (types base) ops := PV_B2_F_MaterializeNative.preserved_93 base request ops
theorem preserved_94 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op94 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op94 (types base) ops := PV_B2_F_MaterializeNative.preserved_94 base request ops
theorem preserved_95 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op95 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op95 (types base) ops := PV_B2_F_MaterializeNative.preserved_95 base request ops
theorem preserved_96 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op96 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op96 (types base) ops := PV_B2_F_MaterializeNative.preserved_96 base request ops
theorem preserved_97 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op97 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op97 (types base) ops := PV_B2_F_MaterializeNative.preserved_97 base request ops
theorem preserved_98 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op98 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op98 (types base) ops := PV_B2_F_MaterializeNative.preserved_98 base request ops
theorem preserved_99 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op99 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op99 (types base) ops := PV_B2_F_MaterializeNative.preserved_99 base request ops
theorem preserved_100 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op100 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op100 (types base) ops := PV_B2_F_MaterializeNative.preserved_100 base request ops
theorem preserved_101 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op101 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op101 (types base) ops := PV_B2_F_MaterializeNative.preserved_101 base request ops
theorem preserved_102 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op102 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op102 (types base) ops := PV_B2_F_MaterializeNative.preserved_102 base request ops
theorem preserved_103 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op103 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op103 (types base) ops := PV_B2_F_MaterializeNative.preserved_103 base request ops
theorem preserved_104 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op104 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op104 (types base) ops := PV_B2_F_MaterializeNative.preserved_104 base request ops
theorem preserved_105 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op105 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op105 (types base) ops := PV_B2_F_MaterializeNative.preserved_105 base request ops
theorem preserved_106 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op106 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op106 (types base) ops := PV_B2_F_MaterializeNative.preserved_106 base request ops
theorem preserved_107 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op107 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op107 (types base) ops := PV_B2_F_MaterializeNative.preserved_107 base request ops
theorem preserved_108 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op108 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op108 (types base) ops := PV_B2_F_MaterializeNative.preserved_108 base request ops
theorem preserved_109 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op109 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op109 (types base) ops := PV_B2_F_MaterializeNative.preserved_109 base request ops
theorem preserved_110 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op110 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op110 (types base) ops := PV_B2_F_MaterializeNative.preserved_110 base request ops
theorem preserved_111 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op111 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op111 (types base) ops := PV_B2_F_MaterializeNative.preserved_111 base request ops
theorem preserved_112 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op112 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op112 (types base) ops := PV_B2_F_MaterializeNative.preserved_112 base request ops
theorem preserved_113 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op113 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op113 (types base) ops := PV_B2_F_MaterializeNative.preserved_113 base request ops
theorem preserved_114 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op114 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op114 (types base) ops := PV_B2_F_MaterializeNative.preserved_114 base request ops
theorem preserved_115 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op115 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op115 (types base) ops := PV_B2_F_MaterializeNative.preserved_115 base request ops
theorem preserved_116 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op116 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op116 (types base) ops := PV_B2_F_MaterializeNative.preserved_116 base request ops
theorem preserved_117 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op117 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op117 (types base) ops := PV_B2_F_MaterializeNative.preserved_117 base request ops
theorem preserved_118 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op118 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op118 (types base) ops := PV_B2_F_MaterializeNative.preserved_118 base request ops
theorem preserved_119 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op119 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op119 (types base) ops := PV_B2_F_MaterializeNative.preserved_119 base request ops
theorem preserved_120 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op120 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op120 (types base) ops := PV_B2_F_MaterializeNative.preserved_120 base request ops
theorem preserved_121 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op121 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op121 (types base) ops := PV_B2_F_MaterializeNative.preserved_121 base request ops
theorem preserved_122 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op122 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op122 (types base) ops := PV_B2_F_MaterializeNative.preserved_122 base request ops
theorem preserved_123 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op123 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op123 (types base) ops := PV_B2_F_MaterializeNative.preserved_123 base request ops
theorem preserved_124 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op124 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op124 (types base) ops := PV_B2_F_MaterializeNative.preserved_124 base request ops
theorem preserved_125 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op125 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op125 (types base) ops := PV_B2_F_MaterializeNative.preserved_125 base request ops
theorem preserved_126 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op126 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op126 (types base) ops := PV_B2_F_MaterializeNative.preserved_126 base request ops
theorem preserved_127 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op127 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op127 (types base) ops := PV_B2_F_MaterializeNative.preserved_127 base request ops
theorem preserved_128 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op128 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op128 (types base) ops := PV_B2_F_MaterializeNative.preserved_128 base request ops
theorem preserved_129 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op129 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op129 (types base) ops := PV_B2_F_MaterializeNative.preserved_129 base request ops
theorem preserved_130 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op130 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op130 (types base) ops := PV_B2_F_MaterializeNative.preserved_130 base request ops
theorem preserved_131 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op131 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op131 (types base) ops := PV_B2_F_MaterializeNative.preserved_131 base request ops
theorem preserved_132 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op132 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op132 (types base) ops := PV_B2_F_MaterializeNative.preserved_132 base request ops
theorem preserved_133 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op133 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op133 (types base) ops := PV_B2_F_MaterializeNative.preserved_133 base request ops
theorem preserved_134 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op134 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op134 (types base) ops := PV_B2_F_MaterializeNative.preserved_134 base request ops
theorem preserved_135 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op135 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op135 (types base) ops := PV_B2_F_MaterializeNative.preserved_135 base request ops
theorem preserved_136 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op136 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op136 (types base) ops := PV_B2_F_MaterializeNative.preserved_136 base request ops
theorem preserved_137 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op137 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op137 (types base) ops := PV_B2_F_MaterializeNative.preserved_137 base request ops
theorem preserved_138 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op138 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op138 (types base) ops := PV_B2_F_MaterializeNative.preserved_138 base request ops
theorem preserved_139 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op139 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op139 (types base) ops := PV_B2_F_MaterializeNative.preserved_139 base request ops
theorem preserved_140 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op140 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op140 (types base) ops := PV_B2_F_MaterializeNative.preserved_140 base request ops
theorem preserved_141 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op141 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op141 (types base) ops := PV_B2_F_MaterializeNative.preserved_141 base request ops
theorem preserved_142 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op142 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op142 (types base) ops := PV_B2_F_MaterializeNative.preserved_142 base request ops
theorem preserved_143 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op143 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op143 (types base) ops := PV_B2_F_MaterializeNative.preserved_143 base request ops
theorem preserved_144 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op144 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op144 (types base) ops := PV_B2_F_MaterializeNative.preserved_144 base request ops
theorem preserved_145 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op145 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op145 (types base) ops := PV_B2_F_MaterializeNative.preserved_145 base request ops
theorem preserved_146 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op146 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op146 (types base) ops := PV_B2_F_MaterializeNative.preserved_146 base request ops
theorem preserved_147 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op147 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op147 (types base) ops := PV_B2_F_MaterializeNative.preserved_147 base request ops
theorem preserved_148 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op148 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op148 (types base) ops := PV_B2_F_MaterializeNative.preserved_148 base request ops
theorem preserved_149 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op149 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op149 (types base) ops := PV_B2_F_MaterializeNative.preserved_149 base request ops
theorem preserved_150 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op150 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op150 (types base) ops := PV_B2_F_MaterializeNative.preserved_150 base request ops
theorem preserved_151 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op151 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op151 (types base) ops := PV_B2_F_MaterializeNative.preserved_151 base request ops
theorem preserved_152 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op152 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op152 (types base) ops := PV_B2_F_MaterializeNative.preserved_152 base request ops
theorem preserved_153 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op153 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op153 (types base) ops := PV_B2_F_MaterializeNative.preserved_153 base request ops
theorem preserved_154 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op154 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op154 (types base) ops := PV_B2_F_MaterializeNative.preserved_154 base request ops
theorem preserved_155 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op155 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op155 (types base) ops := PV_B2_F_MaterializeNative.preserved_155 base request ops
theorem preserved_156 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op156 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op156 (types base) ops := PV_B2_F_MaterializeNative.preserved_156 base request ops
theorem preserved_157 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op157 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op157 (types base) ops := PV_B2_F_MaterializeNative.preserved_157 base request ops
theorem preserved_158 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op158 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op158 (types base) ops := PV_B2_F_MaterializeNative.preserved_158 base request ops
theorem preserved_159 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op159 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op159 (types base) ops := PV_B2_F_MaterializeNative.preserved_159 base request ops
theorem preserved_160 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op160 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op160 (types base) ops := PV_B2_F_MaterializeNative.preserved_160 base request ops
theorem preserved_161 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op161 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op161 (types base) ops := PV_B2_F_MaterializeNative.preserved_161 base request ops
theorem preserved_162 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op162 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op162 (types base) ops := PV_B2_F_MaterializeNative.preserved_162 base request ops
theorem preserved_163 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op163 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op163 (types base) ops := PV_B2_F_MaterializeNative.preserved_163 base request ops
theorem preserved_164 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op164 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op164 (types base) ops := PV_B2_F_MaterializeNative.preserved_164 base request ops
theorem preserved_165 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op165 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op165 (types base) ops := PV_B2_F_MaterializeNative.preserved_165 base request ops
theorem preserved_166 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op166 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op166 (types base) ops := PV_B2_F_MaterializeNative.preserved_166 base request ops
theorem preserved_167 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op167 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op167 (types base) ops := PV_B2_F_MaterializeNative.preserved_167 base request ops
theorem preserved_168 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op168 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op168 (types base) ops := PV_B2_F_MaterializeNative.preserved_168 base request ops
theorem preserved_169 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op169 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op169 (types base) ops := PV_B2_F_MaterializeNative.preserved_169 base request ops
theorem preserved_170 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op170 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op170 (types base) ops := PV_B2_F_MaterializeNative.preserved_170 base request ops
theorem preserved_171 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op171 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op171 (types base) ops := PV_B2_F_MaterializeNative.preserved_171 base request ops
theorem preserved_172 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op172 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op172 (types base) ops := PV_B2_F_MaterializeNative.preserved_172 base request ops
theorem preserved_173 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op173 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op173 (types base) ops := PV_B2_F_MaterializeNative.preserved_173 base request ops
theorem preserved_174 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op174 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op174 (types base) ops := PV_B2_F_MaterializeNative.preserved_174 base request ops
theorem preserved_175 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op175 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op175 (types base) ops := PV_B2_F_MaterializeNative.preserved_175 base request ops
theorem preserved_176 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op176 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op176 (types base) ops := PV_B2_F_MaterializeNative.preserved_176 base request ops
theorem preserved_177 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op177 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op177 (types base) ops := PV_B2_F_MaterializeNative.preserved_177 base request ops
theorem preserved_178 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op178 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op178 (types base) ops := PV_B2_F_MaterializeNative.preserved_178 base request ops
theorem preserved_179 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op179 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op179 (types base) ops := PV_B2_F_MaterializeNative.preserved_179 base request ops
theorem preserved_180 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op180 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op180 (types base) ops := PV_B2_F_MaterializeNative.preserved_180 base request ops
theorem preserved_181 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op181 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op181 (types base) ops := PV_B2_F_MaterializeNative.preserved_181 base request ops
theorem preserved_182 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op182 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op182 (types base) ops := PV_B2_F_MaterializeNative.preserved_182 base request ops
theorem preserved_183 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op183 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op183 (types base) ops := PV_B2_F_MaterializeNative.preserved_183 base request ops
theorem preserved_184 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op184 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op184 (types base) ops := PV_B2_F_MaterializeNative.preserved_184 base request ops
theorem preserved_185 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op185 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op185 (types base) ops := PV_B2_F_MaterializeNative.preserved_185 base request ops
theorem preserved_186 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op186 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op186 (types base) ops := PV_B2_F_MaterializeNative.preserved_186 base request ops
theorem preserved_187 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op187 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op187 (types base) ops := PV_B2_F_MaterializeNative.preserved_187 base request ops
theorem preserved_188 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op188 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op188 (types base) ops := PV_B2_F_MaterializeNative.preserved_188 base request ops
theorem preserved_189 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op189 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op189 (types base) ops := PV_B2_F_MaterializeNative.preserved_189 base request ops
theorem preserved_190 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op190 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op190 (types base) ops := PV_B2_F_MaterializeNative.preserved_190 base request ops
theorem preserved_191 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op191 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op191 (types base) ops := PV_B2_F_MaterializeNative.preserved_191 base request ops
theorem preserved_192 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op192 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op192 (types base) ops := PV_B2_F_MaterializeNative.preserved_192 base request ops
theorem preserved_193 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op193 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op193 (types base) ops := PV_B2_F_MaterializeNative.preserved_193 base request ops
theorem preserved_194 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op194 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op194 (types base) ops := PV_B2_F_MaterializeNative.preserved_194 base request ops
theorem preserved_195 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op195 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op195 (types base) ops := PV_B2_F_MaterializeNative.preserved_195 base request ops
theorem preserved_196 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op196 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op196 (types base) ops := PV_B2_F_MaterializeNative.preserved_196 base request ops
theorem preserved_197 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op197 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op197 (types base) ops := PV_B2_F_MaterializeNative.preserved_197 base request ops
theorem preserved_198 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op198 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op198 (types base) ops := PV_B2_F_MaterializeNative.preserved_198 base request ops
theorem preserved_199 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op199 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op199 (types base) ops := PV_B2_F_MaterializeNative.preserved_199 base request ops
theorem preserved_200 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op200 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op200 (types base) ops := PV_B2_F_MaterializeNative.preserved_200 base request ops
theorem preserved_201 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op201 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op201 (types base) ops := PV_B2_F_MaterializeNative.preserved_201 base request ops
theorem preserved_202 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op202 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op202 (types base) ops := PV_B2_F_MaterializeNative.preserved_202 base request ops
theorem preserved_203 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op203 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op203 (types base) ops := PV_B2_F_MaterializeNative.preserved_203 base request ops
theorem preserved_204 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op204 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op204 (types base) ops := PV_B2_F_MaterializeNative.preserved_204 base request ops
theorem preserved_205 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op205 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op205 (types base) ops := PV_B2_F_MaterializeNative.preserved_205 base request ops
theorem preserved_206 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op206 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op206 (types base) ops := PV_B2_F_MaterializeNative.preserved_206 base request ops
theorem preserved_207 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op207 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op207 (types base) ops := PV_B2_F_MaterializeNative.preserved_207 base request ops
theorem preserved_208 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op208 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op208 (types base) ops := PV_B2_F_MaterializeNative.preserved_208 base request ops
theorem preserved_209 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op209 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op209 (types base) ops := PV_B2_F_MaterializeNative.preserved_209 base request ops
theorem preserved_210 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op210 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op210 (types base) ops := PV_B2_F_MaterializeNative.preserved_210 base request ops
theorem preserved_211 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op211 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op211 (types base) ops := PV_B2_F_MaterializeNative.preserved_211 base request ops
theorem preserved_212 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op212 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op212 (types base) ops := PV_B2_F_MaterializeNative.preserved_212 base request ops
theorem preserved_213 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op213 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op213 (types base) ops := PV_B2_F_MaterializeNative.preserved_213 base request ops
theorem preserved_214 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op214 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op214 (types base) ops := PV_B2_F_MaterializeNative.preserved_214 base request ops
theorem preserved_215 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op215 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op215 (types base) ops := PV_B2_F_MaterializeNative.preserved_215 base request ops
theorem preserved_216 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op216 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op216 (types base) ops := PV_B2_F_MaterializeNative.preserved_216 base request ops
theorem preserved_217 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op217 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op217 (types base) ops := PV_B2_F_MaterializeNative.preserved_217 base request ops
theorem preserved_218 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op218 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op218 (types base) ops := PV_B2_F_MaterializeNative.preserved_218 base request ops
theorem preserved_219 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op219 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op219 (types base) ops := PV_B2_F_MaterializeNative.preserved_219 base request ops
theorem preserved_220 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op220 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op220 (types base) ops := PV_B2_F_MaterializeNative.preserved_220 base request ops
theorem preserved_221 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op221 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op221 (types base) ops := PV_B2_F_MaterializeNative.preserved_221 base request ops
theorem preserved_222 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op222 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op222 (types base) ops := PV_B2_F_MaterializeNative.preserved_222 base request ops
theorem preserved_223 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op223 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op223 (types base) ops := PV_B2_F_MaterializeNative.preserved_223 base request ops
theorem preserved_224 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op224 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op224 (types base) ops := PV_B2_F_MaterializeNative.preserved_224 base request ops
theorem preserved_225 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op225 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op225 (types base) ops := PV_B2_F_MaterializeNative.preserved_225 base request ops
theorem preserved_226 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op226 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op226 (types base) ops := PV_B2_F_MaterializeNative.preserved_226 base request ops
theorem preserved_227 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op227 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op227 (types base) ops := PV_B2_F_MaterializeNative.preserved_227 base request ops
theorem preserved_228 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op228 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op228 (types base) ops := PV_B2_F_MaterializeNative.preserved_228 base request ops
theorem preserved_229 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op229 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op229 (types base) ops := PV_B2_F_MaterializeNative.preserved_229 base request ops
theorem preserved_230 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op230 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op230 (types base) ops := PV_B2_F_MaterializeNative.preserved_230 base request ops
theorem preserved_231 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op231 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op231 (types base) ops := PV_B2_F_MaterializeNative.preserved_231 base request ops
theorem preserved_232 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op232 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op232 (types base) ops := PV_B2_F_MaterializeNative.preserved_232 base request ops
theorem preserved_233 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op233 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op233 (types base) ops := PV_B2_F_MaterializeNative.preserved_233 base request ops
theorem preserved_234 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op234 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op234 (types base) ops := PV_B2_F_MaterializeNative.preserved_234 base request ops
theorem preserved_235 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op235 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op235 (types base) ops := PV_B2_F_MaterializeNative.preserved_235 base request ops
theorem preserved_236 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op236 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op236 (types base) ops := PV_B2_F_MaterializeNative.preserved_236 base request ops
theorem preserved_237 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op237 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op237 (types base) ops := PV_B2_F_MaterializeNative.preserved_237 base request ops
theorem preserved_238 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op238 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op238 (types base) ops := PV_B2_F_MaterializeNative.preserved_238 base request ops
theorem preserved_239 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op239 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op239 (types base) ops := PV_B2_F_MaterializeNative.preserved_239 base request ops
theorem preserved_240 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op240 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op240 (types base) ops := PV_B2_F_MaterializeNative.preserved_240 base request ops
theorem preserved_241 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op241 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op241 (types base) ops := PV_B2_F_MaterializeNative.preserved_241 base request ops
theorem preserved_242 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op242 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op242 (types base) ops := PV_B2_F_MaterializeNative.preserved_242 base request ops
theorem preserved_243 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op243 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op243 (types base) ops := PV_B2_F_MaterializeNative.preserved_243 base request ops
theorem preserved_244 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op244 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op244 (types base) ops := PV_B2_F_MaterializeNative.preserved_244 base request ops
theorem preserved_245 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op245 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op245 (types base) ops := PV_B2_F_MaterializeNative.preserved_245 base request ops
theorem preserved_246 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op246 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op246 (types base) ops := PV_B2_F_MaterializeNative.preserved_246 base request ops
theorem preserved_247 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op247 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op247 (types base) ops := PV_B2_F_MaterializeNative.preserved_247 base request ops
theorem preserved_248 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op248 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op248 (types base) ops := PV_B2_F_MaterializeNative.preserved_248 base request ops
theorem preserved_253 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op253 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op253 (types base) ops := PV_B2_F_MaterializeNative.preserved_253 base request ops
theorem preserved_254 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op254 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op254 (types base) ops := PV_B2_F_MaterializeNative.preserved_254 base request ops
theorem preserved_255 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op255 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op255 (types base) ops := PV_B2_F_MaterializeNative.preserved_255 base request ops
theorem preserved_256 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op256 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op256 (types base) ops := PV_B2_F_MaterializeNative.preserved_256 base request ops
theorem preserved_257 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op257 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op257 (types base) ops := PV_B2_F_MaterializeNative.preserved_257 base request ops
theorem preserved_258 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op258 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op258 (types base) ops := PV_B2_F_MaterializeNative.preserved_258 base request ops
theorem preserved_259 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op259 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op259 (types base) ops := PV_B2_F_MaterializeNative.preserved_259 base request ops
theorem preserved_260 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op260 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op260 (types base) ops := PV_B2_F_MaterializeNative.preserved_260 base request ops
theorem preserved_261 (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op261 (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op261 (types base) ops := PV_B2_F_MaterializeNative.preserved_261 base request ops
#print axioms source
#print axioms value_law
#print axioms nonvacuity
#print axioms failure
#print axioms divergence
#print axioms dictionaries
#print axioms observations
#print axioms preserved_0
#print axioms preserved_1
#print axioms preserved_2
#print axioms preserved_3
#print axioms preserved_4
#print axioms preserved_5
#print axioms preserved_6
#print axioms preserved_7
#print axioms preserved_8
#print axioms preserved_9
#print axioms preserved_10
#print axioms preserved_11
#print axioms preserved_12
#print axioms preserved_13
#print axioms preserved_14
#print axioms preserved_15
#print axioms preserved_16
#print axioms preserved_17
#print axioms preserved_18
#print axioms preserved_19
#print axioms preserved_20
#print axioms preserved_21
#print axioms preserved_22
#print axioms preserved_23
#print axioms preserved_24
#print axioms preserved_25
#print axioms preserved_26
#print axioms preserved_27
#print axioms preserved_28
#print axioms preserved_29
#print axioms preserved_30
#print axioms preserved_31
#print axioms preserved_32
#print axioms preserved_33
#print axioms preserved_34
#print axioms preserved_35
#print axioms preserved_36
#print axioms preserved_37
#print axioms preserved_38
#print axioms preserved_39
#print axioms preserved_40
#print axioms preserved_41
#print axioms preserved_42
#print axioms preserved_43
#print axioms preserved_44
#print axioms preserved_45
#print axioms preserved_46
#print axioms preserved_47
#print axioms preserved_48
#print axioms preserved_49
#print axioms preserved_50
#print axioms preserved_51
#print axioms preserved_52
#print axioms preserved_53
#print axioms preserved_54
#print axioms preserved_55
#print axioms preserved_56
#print axioms preserved_57
#print axioms preserved_58
#print axioms preserved_59
#print axioms preserved_60
#print axioms preserved_61
#print axioms preserved_62
#print axioms preserved_63
#print axioms preserved_64
#print axioms preserved_65
#print axioms preserved_66
#print axioms preserved_67
#print axioms preserved_68
#print axioms preserved_69
#print axioms preserved_70
#print axioms preserved_71
#print axioms preserved_72
#print axioms preserved_73
#print axioms preserved_74
#print axioms preserved_75
#print axioms preserved_76
#print axioms preserved_77
#print axioms preserved_78
#print axioms preserved_79
#print axioms preserved_80
#print axioms preserved_81
#print axioms preserved_82
#print axioms preserved_83
#print axioms preserved_84
#print axioms preserved_85
#print axioms preserved_86
#print axioms preserved_87
#print axioms preserved_88
#print axioms preserved_89
#print axioms preserved_90
#print axioms preserved_91
#print axioms preserved_92
#print axioms preserved_93
#print axioms preserved_94
#print axioms preserved_95
#print axioms preserved_96
#print axioms preserved_97
#print axioms preserved_98
#print axioms preserved_99
#print axioms preserved_100
#print axioms preserved_101
#print axioms preserved_102
#print axioms preserved_103
#print axioms preserved_104
#print axioms preserved_105
#print axioms preserved_106
#print axioms preserved_107
#print axioms preserved_108
#print axioms preserved_109
#print axioms preserved_110
#print axioms preserved_111
#print axioms preserved_112
#print axioms preserved_113
#print axioms preserved_114
#print axioms preserved_115
#print axioms preserved_116
#print axioms preserved_117
#print axioms preserved_118
#print axioms preserved_119
#print axioms preserved_120
#print axioms preserved_121
#print axioms preserved_122
#print axioms preserved_123
#print axioms preserved_124
#print axioms preserved_125
#print axioms preserved_126
#print axioms preserved_127
#print axioms preserved_128
#print axioms preserved_129
#print axioms preserved_130
#print axioms preserved_131
#print axioms preserved_132
#print axioms preserved_133
#print axioms preserved_134
#print axioms preserved_135
#print axioms preserved_136
#print axioms preserved_137
#print axioms preserved_138
#print axioms preserved_139
#print axioms preserved_140
#print axioms preserved_141
#print axioms preserved_142
#print axioms preserved_143
#print axioms preserved_144
#print axioms preserved_145
#print axioms preserved_146
#print axioms preserved_147
#print axioms preserved_148
#print axioms preserved_149
#print axioms preserved_150
#print axioms preserved_151
#print axioms preserved_152
#print axioms preserved_153
#print axioms preserved_154
#print axioms preserved_155
#print axioms preserved_156
#print axioms preserved_157
#print axioms preserved_158
#print axioms preserved_159
#print axioms preserved_160
#print axioms preserved_161
#print axioms preserved_162
#print axioms preserved_163
#print axioms preserved_164
#print axioms preserved_165
#print axioms preserved_166
#print axioms preserved_167
#print axioms preserved_168
#print axioms preserved_169
#print axioms preserved_170
#print axioms preserved_171
#print axioms preserved_172
#print axioms preserved_173
#print axioms preserved_174
#print axioms preserved_175
#print axioms preserved_176
#print axioms preserved_177
#print axioms preserved_178
#print axioms preserved_179
#print axioms preserved_180
#print axioms preserved_181
#print axioms preserved_182
#print axioms preserved_183
#print axioms preserved_184
#print axioms preserved_185
#print axioms preserved_186
#print axioms preserved_187
#print axioms preserved_188
#print axioms preserved_189
#print axioms preserved_190
#print axioms preserved_191
#print axioms preserved_192
#print axioms preserved_193
#print axioms preserved_194
#print axioms preserved_195
#print axioms preserved_196
#print axioms preserved_197
#print axioms preserved_198
#print axioms preserved_199
#print axioms preserved_200
#print axioms preserved_201
#print axioms preserved_202
#print axioms preserved_203
#print axioms preserved_204
#print axioms preserved_205
#print axioms preserved_206
#print axioms preserved_207
#print axioms preserved_208
#print axioms preserved_209
#print axioms preserved_210
#print axioms preserved_211
#print axioms preserved_212
#print axioms preserved_213
#print axioms preserved_214
#print axioms preserved_215
#print axioms preserved_216
#print axioms preserved_217
#print axioms preserved_218
#print axioms preserved_219
#print axioms preserved_220
#print axioms preserved_221
#print axioms preserved_222
#print axioms preserved_223
#print axioms preserved_224
#print axioms preserved_225
#print axioms preserved_226
#print axioms preserved_227
#print axioms preserved_228
#print axioms preserved_229
#print axioms preserved_230
#print axioms preserved_231
#print axioms preserved_232
#print axioms preserved_233
#print axioms preserved_234
#print axioms preserved_235
#print axioms preserved_236
#print axioms preserved_237
#print axioms preserved_238
#print axioms preserved_239
#print axioms preserved_240
#print axioms preserved_241
#print axioms preserved_242
#print axioms preserved_243
#print axioms preserved_244
#print axioms preserved_245
#print axioms preserved_246
#print axioms preserved_247
#print axioms preserved_248
#print axioms preserved_253
#print axioms preserved_254
#print axioms preserved_255
#print axioms preserved_256
#print axioms preserved_257
#print axioms preserved_258
#print axioms preserved_259
#print axioms preserved_260
#print axioms preserved_261
end PV_B2_F_ConstructorNative

end
end
