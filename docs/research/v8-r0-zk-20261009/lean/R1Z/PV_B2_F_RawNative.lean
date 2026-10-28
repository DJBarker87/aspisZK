import R1Z.PV_B2_F_ResourceFamilies
import R1Z.PV_B2_F_RawGuard
import R1Z.PV_B2_D_RawTotal
set_option autoImplicit false
noncomputable section
namespace PV_B2_F_RawNative
open Aeneas Aeneas.Std Result PV_B2_F_ConstructorCarrier
abbrev types := PV_B2_F_ResourceFamilies.types
abbrev HeapRequest := PV_B2_F_ResourceFamilies.HeapRequest
abbrev BoxRequest := PV_B2_F_ResourceFamilies.BoxRequest
abbrev Q := PV_B2_251c1.aspis_core.field.QM31

def toNativeQ (q : Q) : NQ := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def fromNativeQ (q : NQ) : Q := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
theorem roundtrip (q : Q) : fromNativeQ (toNativeQ q)=q := by cases q; rfl
theorem roundtrip_native (q : NQ) : toNativeQ (fromNativeQ q)=q := by cases q; rfl

def callback (w : W) (kind j : Usize) : Result NQ :=
  PV_B2_E_OrdinaryOriginal.mapResult toNativeQ (PV_B2_251c1.host_weights.raw_value w kind j)
def originalCallback (w : W) (kind j : Usize) : Result NQ :=
  PV_B2_E_OrdinaryOriginal.mapResult toNativeQ (PV_B2_F_RawGuard.original w kind j)

def selected (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) : @ProverRwFull.ExternalFuns (types base) :=
  letI : ProverRwFull.ExternalTypes := types base
  {PV_B2_F_ResourceFamilies.selected base heap box ops with op253 := callback}
def originalDictionary (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) : @ProverRwFull.ExternalFuns (types base) :=
  letI : ProverRwFull.ExternalTypes := types base
  {PV_B2_F_ResourceFamilies.originalDictionary base heap box ops with op253 := originalCallback}

/-- Every weight, kind and Usize index; errors/divergence are not filtered. -/
theorem copy_equal_original (w : W) (kind j : Usize) :
    callback w kind j = originalCallback w kind j := by
  unfold callback originalCallback
  rw [PV_B2_F_RawGuard.source]

theorem source (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) (w : W) (kind j : Usize) :
    @ProverRwFull.ExternalFuns.op253 (types base) (selected base heap box ops) w kind j =
      originalCallback w kind j := copy_equal_original w kind j

theorem valid_value_law (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) (w : W) (kind j : Usize)
    (hk : kind.val<7) (hj : j.val<(1024#usize).val) :
    ∃ q, PV_B2_251c1.host_weights.raw_value w kind j = ok q ∧
      @ProverRwFull.ExternalFuns.op253 (types base) (selected base heap box ops) w kind j = ok (toNativeQ q) := by
  obtain ⟨q,hq⟩ := PV_B2_D_RawTotal.source w kind j hk hj
  exact ⟨q,hq,by change PV_B2_E_OrdinaryOriginal.mapResult toNativeQ _ = _;rw [hq];rfl⟩

theorem nonvacuity (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) (w : W) :
    ∃ q, @ProverRwFull.ExternalFuns.op253 (types base) (selected base heap box ops) w 0#usize 0#usize = ok q := by
  obtain ⟨q,_,hq⟩ := valid_value_law base heap box ops w 0#usize 0#usize (by decide) (by decide)
  exact ⟨toNativeQ q,hq⟩

theorem dictionaries (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    selected base heap box ops = originalDictionary base heap box ops := by
  have hc : callback=originalCallback := by funext w kind j;exact copy_equal_original w kind j
  unfold selected originalDictionary
  rw [PV_B2_F_ResourceFamilies.dictionaries,hc]

theorem observations {O : Sort _} (base : ProverRwFull.ExternalTypes)
    (observe : @ProverRwFull.ExternalFuns (types base) → O) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    observe (selected base heap box ops) = observe (originalDictionary base heap box ops) :=
  congrArg observe (dictionaries base heap box ops)
theorem preserved_0 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op0 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op0 (types base) ops := PV_B2_F_ResourceFamilies.preserved_0 base heap box ops
theorem preserved_1 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op1 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op1 (types base) ops := PV_B2_F_ResourceFamilies.preserved_1 base heap box ops
theorem preserved_2 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op2 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op2 (types base) ops := PV_B2_F_ResourceFamilies.preserved_2 base heap box ops
theorem preserved_3 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op3 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op3 (types base) ops := PV_B2_F_ResourceFamilies.preserved_3 base heap box ops
theorem preserved_4 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op4 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op4 (types base) ops := PV_B2_F_ResourceFamilies.preserved_4 base heap box ops
theorem preserved_5 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op5 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op5 (types base) ops := PV_B2_F_ResourceFamilies.preserved_5 base heap box ops
theorem preserved_6 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op6 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op6 (types base) ops := PV_B2_F_ResourceFamilies.preserved_6 base heap box ops
theorem preserved_7 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op7 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op7 (types base) ops := PV_B2_F_ResourceFamilies.preserved_7 base heap box ops
theorem preserved_8 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op8 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op8 (types base) ops := PV_B2_F_ResourceFamilies.preserved_8 base heap box ops
theorem preserved_9 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op9 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op9 (types base) ops := PV_B2_F_ResourceFamilies.preserved_9 base heap box ops
theorem preserved_10 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op10 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op10 (types base) ops := PV_B2_F_ResourceFamilies.preserved_10 base heap box ops
theorem preserved_11 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op11 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op11 (types base) ops := PV_B2_F_ResourceFamilies.preserved_11 base heap box ops
theorem preserved_12 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op12 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op12 (types base) ops := PV_B2_F_ResourceFamilies.preserved_12 base heap box ops
theorem preserved_13 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op13 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op13 (types base) ops := PV_B2_F_ResourceFamilies.preserved_13 base heap box ops
theorem preserved_14 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op14 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op14 (types base) ops := PV_B2_F_ResourceFamilies.preserved_14 base heap box ops
theorem preserved_15 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op15 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op15 (types base) ops := PV_B2_F_ResourceFamilies.preserved_15 base heap box ops
theorem preserved_16 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op16 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op16 (types base) ops := PV_B2_F_ResourceFamilies.preserved_16 base heap box ops
theorem preserved_17 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op17 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op17 (types base) ops := PV_B2_F_ResourceFamilies.preserved_17 base heap box ops
theorem preserved_18 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op18 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op18 (types base) ops := PV_B2_F_ResourceFamilies.preserved_18 base heap box ops
theorem preserved_19 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op19 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op19 (types base) ops := PV_B2_F_ResourceFamilies.preserved_19 base heap box ops
theorem preserved_20 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op20 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op20 (types base) ops := PV_B2_F_ResourceFamilies.preserved_20 base heap box ops
theorem preserved_21 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op21 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op21 (types base) ops := PV_B2_F_ResourceFamilies.preserved_21 base heap box ops
theorem preserved_22 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op22 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op22 (types base) ops := PV_B2_F_ResourceFamilies.preserved_22 base heap box ops
theorem preserved_23 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op23 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op23 (types base) ops := PV_B2_F_ResourceFamilies.preserved_23 base heap box ops
theorem preserved_24 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op24 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op24 (types base) ops := PV_B2_F_ResourceFamilies.preserved_24 base heap box ops
theorem preserved_25 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op25 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op25 (types base) ops := PV_B2_F_ResourceFamilies.preserved_25 base heap box ops
theorem preserved_26 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op26 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op26 (types base) ops := PV_B2_F_ResourceFamilies.preserved_26 base heap box ops
theorem preserved_27 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op27 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op27 (types base) ops := PV_B2_F_ResourceFamilies.preserved_27 base heap box ops
theorem preserved_28 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op28 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op28 (types base) ops := PV_B2_F_ResourceFamilies.preserved_28 base heap box ops
theorem preserved_29 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op29 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op29 (types base) ops := PV_B2_F_ResourceFamilies.preserved_29 base heap box ops
theorem preserved_30 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op30 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op30 (types base) ops := PV_B2_F_ResourceFamilies.preserved_30 base heap box ops
theorem preserved_31 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op31 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op31 (types base) ops := PV_B2_F_ResourceFamilies.preserved_31 base heap box ops
theorem preserved_32 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op32 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op32 (types base) ops := PV_B2_F_ResourceFamilies.preserved_32 base heap box ops
theorem preserved_33 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op33 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op33 (types base) ops := PV_B2_F_ResourceFamilies.preserved_33 base heap box ops
theorem preserved_34 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op34 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op34 (types base) ops := PV_B2_F_ResourceFamilies.preserved_34 base heap box ops
theorem preserved_35 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op35 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op35 (types base) ops := PV_B2_F_ResourceFamilies.preserved_35 base heap box ops
theorem preserved_36 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op36 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op36 (types base) ops := PV_B2_F_ResourceFamilies.preserved_36 base heap box ops
theorem preserved_37 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op37 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op37 (types base) ops := PV_B2_F_ResourceFamilies.preserved_37 base heap box ops
theorem preserved_38 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op38 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op38 (types base) ops := PV_B2_F_ResourceFamilies.preserved_38 base heap box ops
theorem preserved_39 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op39 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op39 (types base) ops := PV_B2_F_ResourceFamilies.preserved_39 base heap box ops
theorem preserved_40 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op40 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op40 (types base) ops := PV_B2_F_ResourceFamilies.preserved_40 base heap box ops
theorem preserved_41 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op41 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op41 (types base) ops := PV_B2_F_ResourceFamilies.preserved_41 base heap box ops
theorem preserved_42 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op42 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op42 (types base) ops := PV_B2_F_ResourceFamilies.preserved_42 base heap box ops
theorem preserved_43 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op43 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op43 (types base) ops := PV_B2_F_ResourceFamilies.preserved_43 base heap box ops
theorem preserved_44 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op44 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op44 (types base) ops := PV_B2_F_ResourceFamilies.preserved_44 base heap box ops
theorem preserved_45 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op45 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op45 (types base) ops := PV_B2_F_ResourceFamilies.preserved_45 base heap box ops
theorem preserved_46 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op46 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op46 (types base) ops := PV_B2_F_ResourceFamilies.preserved_46 base heap box ops
theorem preserved_47 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op47 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op47 (types base) ops := PV_B2_F_ResourceFamilies.preserved_47 base heap box ops
theorem preserved_48 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op48 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op48 (types base) ops := PV_B2_F_ResourceFamilies.preserved_48 base heap box ops
theorem preserved_49 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op49 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op49 (types base) ops := PV_B2_F_ResourceFamilies.preserved_49 base heap box ops
theorem preserved_50 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op50 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op50 (types base) ops := PV_B2_F_ResourceFamilies.preserved_50 base heap box ops
theorem preserved_51 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op51 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op51 (types base) ops := PV_B2_F_ResourceFamilies.preserved_51 base heap box ops
theorem preserved_52 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op52 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op52 (types base) ops := PV_B2_F_ResourceFamilies.preserved_52 base heap box ops
theorem preserved_53 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op53 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op53 (types base) ops := PV_B2_F_ResourceFamilies.preserved_53 base heap box ops
theorem preserved_54 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op54 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op54 (types base) ops := PV_B2_F_ResourceFamilies.preserved_54 base heap box ops
theorem preserved_55 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op55 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op55 (types base) ops := PV_B2_F_ResourceFamilies.preserved_55 base heap box ops
theorem preserved_56 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op56 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op56 (types base) ops := PV_B2_F_ResourceFamilies.preserved_56 base heap box ops
theorem preserved_57 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op57 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op57 (types base) ops := PV_B2_F_ResourceFamilies.preserved_57 base heap box ops
theorem preserved_58 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op58 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op58 (types base) ops := PV_B2_F_ResourceFamilies.preserved_58 base heap box ops
theorem preserved_59 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op59 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op59 (types base) ops := PV_B2_F_ResourceFamilies.preserved_59 base heap box ops
theorem preserved_60 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op60 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op60 (types base) ops := PV_B2_F_ResourceFamilies.preserved_60 base heap box ops
theorem preserved_61 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op61 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op61 (types base) ops := PV_B2_F_ResourceFamilies.preserved_61 base heap box ops
theorem preserved_62 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op62 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op62 (types base) ops := PV_B2_F_ResourceFamilies.preserved_62 base heap box ops
theorem preserved_63 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op63 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op63 (types base) ops := PV_B2_F_ResourceFamilies.preserved_63 base heap box ops
theorem preserved_64 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op64 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op64 (types base) ops := PV_B2_F_ResourceFamilies.preserved_64 base heap box ops
theorem preserved_65 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op65 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op65 (types base) ops := PV_B2_F_ResourceFamilies.preserved_65 base heap box ops
theorem preserved_66 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op66 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op66 (types base) ops := PV_B2_F_ResourceFamilies.preserved_66 base heap box ops
theorem preserved_67 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op67 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op67 (types base) ops := PV_B2_F_ResourceFamilies.preserved_67 base heap box ops
theorem preserved_68 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op68 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op68 (types base) ops := PV_B2_F_ResourceFamilies.preserved_68 base heap box ops
theorem preserved_69 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op69 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op69 (types base) ops := PV_B2_F_ResourceFamilies.preserved_69 base heap box ops
theorem preserved_70 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op70 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op70 (types base) ops := PV_B2_F_ResourceFamilies.preserved_70 base heap box ops
theorem preserved_71 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op71 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op71 (types base) ops := PV_B2_F_ResourceFamilies.preserved_71 base heap box ops
theorem preserved_72 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op72 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op72 (types base) ops := PV_B2_F_ResourceFamilies.preserved_72 base heap box ops
theorem preserved_73 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op73 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op73 (types base) ops := PV_B2_F_ResourceFamilies.preserved_73 base heap box ops
theorem preserved_74 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op74 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op74 (types base) ops := PV_B2_F_ResourceFamilies.preserved_74 base heap box ops
theorem preserved_75 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op75 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op75 (types base) ops := PV_B2_F_ResourceFamilies.preserved_75 base heap box ops
theorem preserved_76 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op76 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op76 (types base) ops := PV_B2_F_ResourceFamilies.preserved_76 base heap box ops
theorem preserved_77 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op77 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op77 (types base) ops := PV_B2_F_ResourceFamilies.preserved_77 base heap box ops
theorem preserved_78 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op78 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op78 (types base) ops := PV_B2_F_ResourceFamilies.preserved_78 base heap box ops
theorem preserved_79 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op79 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op79 (types base) ops := PV_B2_F_ResourceFamilies.preserved_79 base heap box ops
theorem preserved_80 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op80 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op80 (types base) ops := PV_B2_F_ResourceFamilies.preserved_80 base heap box ops
theorem preserved_81 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op81 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op81 (types base) ops := PV_B2_F_ResourceFamilies.preserved_81 base heap box ops
theorem preserved_82 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op82 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op82 (types base) ops := PV_B2_F_ResourceFamilies.preserved_82 base heap box ops
theorem preserved_83 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op83 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op83 (types base) ops := PV_B2_F_ResourceFamilies.preserved_83 base heap box ops
theorem preserved_84 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op84 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op84 (types base) ops := PV_B2_F_ResourceFamilies.preserved_84 base heap box ops
theorem preserved_85 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op85 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op85 (types base) ops := PV_B2_F_ResourceFamilies.preserved_85 base heap box ops
theorem preserved_86 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op86 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op86 (types base) ops := PV_B2_F_ResourceFamilies.preserved_86 base heap box ops
theorem preserved_87 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op87 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op87 (types base) ops := PV_B2_F_ResourceFamilies.preserved_87 base heap box ops
theorem preserved_88 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op88 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op88 (types base) ops := PV_B2_F_ResourceFamilies.preserved_88 base heap box ops
theorem preserved_89 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op89 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op89 (types base) ops := PV_B2_F_ResourceFamilies.preserved_89 base heap box ops
theorem preserved_90 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op90 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op90 (types base) ops := PV_B2_F_ResourceFamilies.preserved_90 base heap box ops
theorem preserved_91 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op91 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op91 (types base) ops := PV_B2_F_ResourceFamilies.preserved_91 base heap box ops
theorem preserved_92 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op92 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op92 (types base) ops := PV_B2_F_ResourceFamilies.preserved_92 base heap box ops
theorem preserved_93 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op93 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op93 (types base) ops := PV_B2_F_ResourceFamilies.preserved_93 base heap box ops
theorem preserved_94 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op94 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op94 (types base) ops := PV_B2_F_ResourceFamilies.preserved_94 base heap box ops
theorem preserved_95 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op95 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op95 (types base) ops := PV_B2_F_ResourceFamilies.preserved_95 base heap box ops
theorem preserved_96 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op96 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op96 (types base) ops := PV_B2_F_ResourceFamilies.preserved_96 base heap box ops
theorem preserved_97 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op97 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op97 (types base) ops := PV_B2_F_ResourceFamilies.preserved_97 base heap box ops
theorem preserved_98 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op98 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op98 (types base) ops := PV_B2_F_ResourceFamilies.preserved_98 base heap box ops
theorem preserved_99 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op99 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op99 (types base) ops := PV_B2_F_ResourceFamilies.preserved_99 base heap box ops
theorem preserved_100 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op100 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op100 (types base) ops := PV_B2_F_ResourceFamilies.preserved_100 base heap box ops
theorem preserved_101 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op101 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op101 (types base) ops := PV_B2_F_ResourceFamilies.preserved_101 base heap box ops
theorem preserved_102 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op102 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op102 (types base) ops := PV_B2_F_ResourceFamilies.preserved_102 base heap box ops
theorem preserved_103 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op103 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op103 (types base) ops := PV_B2_F_ResourceFamilies.preserved_103 base heap box ops
theorem preserved_104 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op104 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op104 (types base) ops := PV_B2_F_ResourceFamilies.preserved_104 base heap box ops
theorem preserved_105 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op105 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op105 (types base) ops := PV_B2_F_ResourceFamilies.preserved_105 base heap box ops
theorem preserved_106 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op106 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op106 (types base) ops := PV_B2_F_ResourceFamilies.preserved_106 base heap box ops
theorem preserved_107 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op107 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op107 (types base) ops := PV_B2_F_ResourceFamilies.preserved_107 base heap box ops
theorem preserved_108 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op108 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op108 (types base) ops := PV_B2_F_ResourceFamilies.preserved_108 base heap box ops
theorem preserved_109 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op109 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op109 (types base) ops := PV_B2_F_ResourceFamilies.preserved_109 base heap box ops
theorem preserved_110 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op110 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op110 (types base) ops := PV_B2_F_ResourceFamilies.preserved_110 base heap box ops
theorem preserved_111 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op111 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op111 (types base) ops := PV_B2_F_ResourceFamilies.preserved_111 base heap box ops
theorem preserved_112 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op112 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op112 (types base) ops := PV_B2_F_ResourceFamilies.preserved_112 base heap box ops
theorem preserved_113 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op113 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op113 (types base) ops := PV_B2_F_ResourceFamilies.preserved_113 base heap box ops
theorem preserved_114 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op114 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op114 (types base) ops := PV_B2_F_ResourceFamilies.preserved_114 base heap box ops
theorem preserved_115 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op115 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op115 (types base) ops := PV_B2_F_ResourceFamilies.preserved_115 base heap box ops
theorem preserved_116 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op116 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op116 (types base) ops := PV_B2_F_ResourceFamilies.preserved_116 base heap box ops
theorem preserved_117 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op117 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op117 (types base) ops := PV_B2_F_ResourceFamilies.preserved_117 base heap box ops
theorem preserved_118 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op118 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op118 (types base) ops := PV_B2_F_ResourceFamilies.preserved_118 base heap box ops
theorem preserved_119 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op119 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op119 (types base) ops := PV_B2_F_ResourceFamilies.preserved_119 base heap box ops
theorem preserved_120 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op120 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op120 (types base) ops := PV_B2_F_ResourceFamilies.preserved_120 base heap box ops
theorem preserved_121 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op121 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op121 (types base) ops := PV_B2_F_ResourceFamilies.preserved_121 base heap box ops
theorem preserved_122 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op122 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op122 (types base) ops := PV_B2_F_ResourceFamilies.preserved_122 base heap box ops
theorem preserved_123 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op123 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op123 (types base) ops := PV_B2_F_ResourceFamilies.preserved_123 base heap box ops
theorem preserved_124 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op124 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op124 (types base) ops := PV_B2_F_ResourceFamilies.preserved_124 base heap box ops
theorem preserved_125 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op125 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op125 (types base) ops := PV_B2_F_ResourceFamilies.preserved_125 base heap box ops
theorem preserved_126 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op126 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op126 (types base) ops := PV_B2_F_ResourceFamilies.preserved_126 base heap box ops
theorem preserved_127 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op127 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op127 (types base) ops := PV_B2_F_ResourceFamilies.preserved_127 base heap box ops
theorem preserved_128 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op128 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op128 (types base) ops := PV_B2_F_ResourceFamilies.preserved_128 base heap box ops
theorem preserved_129 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op129 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op129 (types base) ops := PV_B2_F_ResourceFamilies.preserved_129 base heap box ops
theorem preserved_130 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op130 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op130 (types base) ops := PV_B2_F_ResourceFamilies.preserved_130 base heap box ops
theorem preserved_131 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op131 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op131 (types base) ops := PV_B2_F_ResourceFamilies.preserved_131 base heap box ops
theorem preserved_132 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op132 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op132 (types base) ops := PV_B2_F_ResourceFamilies.preserved_132 base heap box ops
theorem preserved_133 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op133 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op133 (types base) ops := PV_B2_F_ResourceFamilies.preserved_133 base heap box ops
theorem preserved_134 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op134 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op134 (types base) ops := PV_B2_F_ResourceFamilies.preserved_134 base heap box ops
theorem preserved_135 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op135 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op135 (types base) ops := PV_B2_F_ResourceFamilies.preserved_135 base heap box ops
theorem preserved_136 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op136 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op136 (types base) ops := PV_B2_F_ResourceFamilies.preserved_136 base heap box ops
theorem preserved_137 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op137 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op137 (types base) ops := PV_B2_F_ResourceFamilies.preserved_137 base heap box ops
theorem preserved_138 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op138 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op138 (types base) ops := PV_B2_F_ResourceFamilies.preserved_138 base heap box ops
theorem preserved_139 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op139 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op139 (types base) ops := PV_B2_F_ResourceFamilies.preserved_139 base heap box ops
theorem preserved_140 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op140 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op140 (types base) ops := PV_B2_F_ResourceFamilies.preserved_140 base heap box ops
theorem preserved_141 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op141 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op141 (types base) ops := PV_B2_F_ResourceFamilies.preserved_141 base heap box ops
theorem preserved_142 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op142 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op142 (types base) ops := PV_B2_F_ResourceFamilies.preserved_142 base heap box ops
theorem preserved_143 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op143 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op143 (types base) ops := PV_B2_F_ResourceFamilies.preserved_143 base heap box ops
theorem preserved_144 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op144 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op144 (types base) ops := PV_B2_F_ResourceFamilies.preserved_144 base heap box ops
theorem preserved_145 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op145 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op145 (types base) ops := PV_B2_F_ResourceFamilies.preserved_145 base heap box ops
theorem preserved_146 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op146 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op146 (types base) ops := PV_B2_F_ResourceFamilies.preserved_146 base heap box ops
theorem preserved_147 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op147 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op147 (types base) ops := PV_B2_F_ResourceFamilies.preserved_147 base heap box ops
theorem preserved_148 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op148 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op148 (types base) ops := PV_B2_F_ResourceFamilies.preserved_148 base heap box ops
theorem preserved_149 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op149 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op149 (types base) ops := PV_B2_F_ResourceFamilies.preserved_149 base heap box ops
theorem preserved_150 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op150 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op150 (types base) ops := PV_B2_F_ResourceFamilies.preserved_150 base heap box ops
theorem preserved_151 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op151 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op151 (types base) ops := PV_B2_F_ResourceFamilies.preserved_151 base heap box ops
theorem preserved_152 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op152 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op152 (types base) ops := PV_B2_F_ResourceFamilies.preserved_152 base heap box ops
theorem preserved_153 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op153 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op153 (types base) ops := PV_B2_F_ResourceFamilies.preserved_153 base heap box ops
theorem preserved_154 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op154 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op154 (types base) ops := PV_B2_F_ResourceFamilies.preserved_154 base heap box ops
theorem preserved_155 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op155 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op155 (types base) ops := PV_B2_F_ResourceFamilies.preserved_155 base heap box ops
theorem preserved_156 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op156 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op156 (types base) ops := PV_B2_F_ResourceFamilies.preserved_156 base heap box ops
theorem preserved_157 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op157 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op157 (types base) ops := PV_B2_F_ResourceFamilies.preserved_157 base heap box ops
theorem preserved_158 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op158 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op158 (types base) ops := PV_B2_F_ResourceFamilies.preserved_158 base heap box ops
theorem preserved_159 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op159 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op159 (types base) ops := PV_B2_F_ResourceFamilies.preserved_159 base heap box ops
theorem preserved_160 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op160 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op160 (types base) ops := PV_B2_F_ResourceFamilies.preserved_160 base heap box ops
theorem preserved_161 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op161 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op161 (types base) ops := PV_B2_F_ResourceFamilies.preserved_161 base heap box ops
theorem preserved_162 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op162 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op162 (types base) ops := PV_B2_F_ResourceFamilies.preserved_162 base heap box ops
theorem preserved_163 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op163 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op163 (types base) ops := PV_B2_F_ResourceFamilies.preserved_163 base heap box ops
theorem preserved_164 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op164 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op164 (types base) ops := PV_B2_F_ResourceFamilies.preserved_164 base heap box ops
theorem preserved_165 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op165 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op165 (types base) ops := PV_B2_F_ResourceFamilies.preserved_165 base heap box ops
theorem preserved_166 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op166 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op166 (types base) ops := PV_B2_F_ResourceFamilies.preserved_166 base heap box ops
theorem preserved_167 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op167 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op167 (types base) ops := PV_B2_F_ResourceFamilies.preserved_167 base heap box ops
theorem preserved_168 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op168 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op168 (types base) ops := PV_B2_F_ResourceFamilies.preserved_168 base heap box ops
theorem preserved_169 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op169 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op169 (types base) ops := PV_B2_F_ResourceFamilies.preserved_169 base heap box ops
theorem preserved_170 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op170 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op170 (types base) ops := PV_B2_F_ResourceFamilies.preserved_170 base heap box ops
theorem preserved_171 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op171 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op171 (types base) ops := PV_B2_F_ResourceFamilies.preserved_171 base heap box ops
theorem preserved_172 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op172 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op172 (types base) ops := PV_B2_F_ResourceFamilies.preserved_172 base heap box ops
theorem preserved_173 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op173 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op173 (types base) ops := PV_B2_F_ResourceFamilies.preserved_173 base heap box ops
theorem preserved_174 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op174 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op174 (types base) ops := PV_B2_F_ResourceFamilies.preserved_174 base heap box ops
theorem preserved_175 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op175 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op175 (types base) ops := PV_B2_F_ResourceFamilies.preserved_175 base heap box ops
theorem preserved_176 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op176 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op176 (types base) ops := PV_B2_F_ResourceFamilies.preserved_176 base heap box ops
theorem preserved_177 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op177 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op177 (types base) ops := PV_B2_F_ResourceFamilies.preserved_177 base heap box ops
theorem preserved_178 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op178 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op178 (types base) ops := PV_B2_F_ResourceFamilies.preserved_178 base heap box ops
theorem preserved_179 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op179 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op179 (types base) ops := PV_B2_F_ResourceFamilies.preserved_179 base heap box ops
theorem preserved_180 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op180 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op180 (types base) ops := PV_B2_F_ResourceFamilies.preserved_180 base heap box ops
theorem preserved_181 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op181 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op181 (types base) ops := PV_B2_F_ResourceFamilies.preserved_181 base heap box ops
theorem preserved_182 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op182 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op182 (types base) ops := PV_B2_F_ResourceFamilies.preserved_182 base heap box ops
theorem preserved_183 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op183 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op183 (types base) ops := PV_B2_F_ResourceFamilies.preserved_183 base heap box ops
theorem preserved_184 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op184 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op184 (types base) ops := PV_B2_F_ResourceFamilies.preserved_184 base heap box ops
theorem preserved_185 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op185 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op185 (types base) ops := PV_B2_F_ResourceFamilies.preserved_185 base heap box ops
theorem preserved_186 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op186 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op186 (types base) ops := PV_B2_F_ResourceFamilies.preserved_186 base heap box ops
theorem preserved_187 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op187 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op187 (types base) ops := PV_B2_F_ResourceFamilies.preserved_187 base heap box ops
theorem preserved_188 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op188 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op188 (types base) ops := PV_B2_F_ResourceFamilies.preserved_188 base heap box ops
theorem preserved_189 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op189 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op189 (types base) ops := PV_B2_F_ResourceFamilies.preserved_189 base heap box ops
theorem preserved_190 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op190 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op190 (types base) ops := PV_B2_F_ResourceFamilies.preserved_190 base heap box ops
theorem preserved_191 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op191 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op191 (types base) ops := PV_B2_F_ResourceFamilies.preserved_191 base heap box ops
theorem preserved_192 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op192 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op192 (types base) ops := PV_B2_F_ResourceFamilies.preserved_192 base heap box ops
theorem preserved_193 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op193 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op193 (types base) ops := PV_B2_F_ResourceFamilies.preserved_193 base heap box ops
theorem preserved_194 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op194 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op194 (types base) ops := PV_B2_F_ResourceFamilies.preserved_194 base heap box ops
theorem preserved_195 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op195 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op195 (types base) ops := PV_B2_F_ResourceFamilies.preserved_195 base heap box ops
theorem preserved_196 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op196 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op196 (types base) ops := PV_B2_F_ResourceFamilies.preserved_196 base heap box ops
theorem preserved_197 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op197 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op197 (types base) ops := PV_B2_F_ResourceFamilies.preserved_197 base heap box ops
theorem preserved_198 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op198 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op198 (types base) ops := PV_B2_F_ResourceFamilies.preserved_198 base heap box ops
theorem preserved_199 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op199 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op199 (types base) ops := PV_B2_F_ResourceFamilies.preserved_199 base heap box ops
theorem preserved_200 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op200 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op200 (types base) ops := PV_B2_F_ResourceFamilies.preserved_200 base heap box ops
theorem preserved_201 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op201 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op201 (types base) ops := PV_B2_F_ResourceFamilies.preserved_201 base heap box ops
theorem preserved_202 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op202 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op202 (types base) ops := PV_B2_F_ResourceFamilies.preserved_202 base heap box ops
theorem preserved_203 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op203 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op203 (types base) ops := PV_B2_F_ResourceFamilies.preserved_203 base heap box ops
theorem preserved_204 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op204 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op204 (types base) ops := PV_B2_F_ResourceFamilies.preserved_204 base heap box ops
theorem preserved_205 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op205 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op205 (types base) ops := PV_B2_F_ResourceFamilies.preserved_205 base heap box ops
theorem preserved_206 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op206 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op206 (types base) ops := PV_B2_F_ResourceFamilies.preserved_206 base heap box ops
theorem preserved_207 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op207 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op207 (types base) ops := PV_B2_F_ResourceFamilies.preserved_207 base heap box ops
theorem preserved_208 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op208 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op208 (types base) ops := PV_B2_F_ResourceFamilies.preserved_208 base heap box ops
theorem preserved_209 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op209 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op209 (types base) ops := PV_B2_F_ResourceFamilies.preserved_209 base heap box ops
theorem preserved_210 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op210 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op210 (types base) ops := PV_B2_F_ResourceFamilies.preserved_210 base heap box ops
theorem preserved_211 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op211 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op211 (types base) ops := PV_B2_F_ResourceFamilies.preserved_211 base heap box ops
theorem preserved_212 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op212 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op212 (types base) ops := PV_B2_F_ResourceFamilies.preserved_212 base heap box ops
theorem preserved_213 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op213 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op213 (types base) ops := PV_B2_F_ResourceFamilies.preserved_213 base heap box ops
theorem preserved_214 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op214 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op214 (types base) ops := PV_B2_F_ResourceFamilies.preserved_214 base heap box ops
theorem preserved_215 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op215 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op215 (types base) ops := PV_B2_F_ResourceFamilies.preserved_215 base heap box ops
theorem preserved_216 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op216 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op216 (types base) ops := PV_B2_F_ResourceFamilies.preserved_216 base heap box ops
theorem preserved_217 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op217 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op217 (types base) ops := PV_B2_F_ResourceFamilies.preserved_217 base heap box ops
theorem preserved_218 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op218 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op218 (types base) ops := PV_B2_F_ResourceFamilies.preserved_218 base heap box ops
theorem preserved_219 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op219 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op219 (types base) ops := PV_B2_F_ResourceFamilies.preserved_219 base heap box ops
theorem preserved_220 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op220 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op220 (types base) ops := PV_B2_F_ResourceFamilies.preserved_220 base heap box ops
theorem preserved_221 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op221 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op221 (types base) ops := PV_B2_F_ResourceFamilies.preserved_221 base heap box ops
theorem preserved_222 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op222 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op222 (types base) ops := PV_B2_F_ResourceFamilies.preserved_222 base heap box ops
theorem preserved_223 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op223 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op223 (types base) ops := PV_B2_F_ResourceFamilies.preserved_223 base heap box ops
theorem preserved_224 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op224 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op224 (types base) ops := PV_B2_F_ResourceFamilies.preserved_224 base heap box ops
theorem preserved_225 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op225 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op225 (types base) ops := PV_B2_F_ResourceFamilies.preserved_225 base heap box ops
theorem preserved_226 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op226 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op226 (types base) ops := PV_B2_F_ResourceFamilies.preserved_226 base heap box ops
theorem preserved_227 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op227 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op227 (types base) ops := PV_B2_F_ResourceFamilies.preserved_227 base heap box ops
theorem preserved_228 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op228 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op228 (types base) ops := PV_B2_F_ResourceFamilies.preserved_228 base heap box ops
theorem preserved_229 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op229 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op229 (types base) ops := PV_B2_F_ResourceFamilies.preserved_229 base heap box ops
theorem preserved_230 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op230 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op230 (types base) ops := PV_B2_F_ResourceFamilies.preserved_230 base heap box ops
theorem preserved_231 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op231 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op231 (types base) ops := PV_B2_F_ResourceFamilies.preserved_231 base heap box ops
theorem preserved_232 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op232 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op232 (types base) ops := PV_B2_F_ResourceFamilies.preserved_232 base heap box ops
theorem preserved_233 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op233 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op233 (types base) ops := PV_B2_F_ResourceFamilies.preserved_233 base heap box ops
theorem preserved_234 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op234 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op234 (types base) ops := PV_B2_F_ResourceFamilies.preserved_234 base heap box ops
theorem preserved_235 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op235 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op235 (types base) ops := PV_B2_F_ResourceFamilies.preserved_235 base heap box ops
theorem preserved_236 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op236 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op236 (types base) ops := PV_B2_F_ResourceFamilies.preserved_236 base heap box ops
theorem preserved_237 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op237 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op237 (types base) ops := PV_B2_F_ResourceFamilies.preserved_237 base heap box ops
theorem preserved_238 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op238 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op238 (types base) ops := PV_B2_F_ResourceFamilies.preserved_238 base heap box ops
theorem preserved_239 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op239 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op239 (types base) ops := PV_B2_F_ResourceFamilies.preserved_239 base heap box ops
theorem preserved_240 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op240 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op240 (types base) ops := PV_B2_F_ResourceFamilies.preserved_240 base heap box ops
theorem preserved_241 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op241 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op241 (types base) ops := PV_B2_F_ResourceFamilies.preserved_241 base heap box ops
theorem preserved_242 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op242 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op242 (types base) ops := PV_B2_F_ResourceFamilies.preserved_242 base heap box ops
theorem preserved_243 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op243 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op243 (types base) ops := PV_B2_F_ResourceFamilies.preserved_243 base heap box ops
theorem preserved_244 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op244 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op244 (types base) ops := PV_B2_F_ResourceFamilies.preserved_244 base heap box ops
theorem preserved_245 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op245 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op245 (types base) ops := PV_B2_F_ResourceFamilies.preserved_245 base heap box ops
theorem preserved_246 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op246 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op246 (types base) ops := PV_B2_F_ResourceFamilies.preserved_246 base heap box ops
theorem preserved_247 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op247 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op247 (types base) ops := PV_B2_F_ResourceFamilies.preserved_247 base heap box ops
theorem preserved_248 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op248 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op248 (types base) ops := PV_B2_F_ResourceFamilies.preserved_248 base heap box ops
theorem preserved_254 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op254 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op254 (types base) ops := PV_B2_F_ResourceFamilies.preserved_254 base heap box ops
theorem preserved_255 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op255 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op255 (types base) ops := PV_B2_F_ResourceFamilies.preserved_255 base heap box ops
theorem preserved_256 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op256 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op256 (types base) ops := PV_B2_F_ResourceFamilies.preserved_256 base heap box ops
theorem preserved_257 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op257 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op257 (types base) ops := PV_B2_F_ResourceFamilies.preserved_257 base heap box ops
theorem preserved_258 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op258 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op258 (types base) ops := PV_B2_F_ResourceFamilies.preserved_258 base heap box ops
theorem preserved_259 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op259 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op259 (types base) ops := PV_B2_F_ResourceFamilies.preserved_259 base heap box ops
theorem preserved_260 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op260 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op260 (types base) ops := PV_B2_F_ResourceFamilies.preserved_260 base heap box ops
theorem preserved_261 (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op261 (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op261 (types base) ops := PV_B2_F_ResourceFamilies.preserved_261 base heap box ops
#print axioms roundtrip
#print axioms roundtrip_native
#print axioms copy_equal_original
#print axioms source
#print axioms valid_value_law
#print axioms nonvacuity
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
#print axioms preserved_254
#print axioms preserved_255
#print axioms preserved_256
#print axioms preserved_257
#print axioms preserved_258
#print axioms preserved_259
#print axioms preserved_260
#print axioms preserved_261
end PV_B2_F_RawNative
