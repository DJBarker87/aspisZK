import R1Z.PV_RDB2D_SamplerCore
import R1Z.PV_RDB2D_Install250
set_option autoImplicit false
noncomputable section
namespace PV_B2_E_GammaOriginal
open Aeneas Aeneas.Std Result
open PV_B2_C_GammaNumeric
open PV_B2_E_OrdinaryOriginal

/-- Structural frozen gamma control with owned-state iterator transport and the
original reducing decoder. It is not the defective original iterator emission. -/
def originalOps : GammaHelpers Raw where
  low := PV_B2_C_OrdinaryReference.sampler_owned.low_base_p_digits
  add := PV_B2_C_Sampler.host_sampler.add_small_base_p
  decode := fun a => ok (decode a)
def originalGamma (b : Bytes) : Result Raw := sample originalOps b

theorem refines : HelpersRefine originalOps where
  low := by
    intro b a q h
    apply PV_B2_C_GammaHelpers.low_refines b a q
    change PV_B2_C_Sampler.host_sampler.low_base_p_digits b = _
    rw [PV_B2_C_LowDigits.source]
    exact h
  add := PV_B2_C_GammaHelpers.add_refines

theorem total : HelpersTotal originalOps where
  low := by
    intro b
    obtain ⟨a,q,h⟩ := PV_B2_C_GammaHelpers.total_source.low b
    exact ⟨a,q,(PV_B2_C_LowDigits.source b).symm.trans h⟩
  add := PV_B2_C_GammaHelpers.total_source.add
  decode := by intro a _; exact ⟨decode a,rfl⟩

theorem values_injective {a b : PV_B2_C_GammaNumeric.Digits}
    (h : values a = values b) : a = b := by
  apply Subtype.ext
  exact (List.map_inj_right (f := fun x : U32 => x.val)
    (fun _ _ hv => UScalar.eq_of_val_eq hv)).mp h

/-- Universal frozen structural original/copy Result equality: every byte block,
with no assumed success, limb bounds, rank law or callback correspondence. -/
theorem copy_equal_original (b : Bytes) :
    PV_B2_C_249.host_sampler.gamma_sample b = originalGamma b := by
  obtain ⟨out,he⟩ := sample_total PV_B2_C_GammaHelpers.ops
    PV_B2_C_GammaHelpers.refine_source PV_B2_C_GammaHelpers.total_source b
  obtain ⟨a,hd,hv⟩ := gamma_digits_success PV_B2_C_GammaHelpers.ops
    PV_B2_C_GammaHelpers.refine_source b out he
  obtain ⟨old,ho⟩ := sample_total originalOps refines total b
  obtain ⟨c,hc,hcv⟩ := gamma_digits_success originalOps refines b old ho
  have hac : a = c := values_injective (hv.trans hcv.symm)
  subst c
  -- Obtain canonicality at the exact final digit array using the common value law.
  have ha : Canonical a := by
    unfold Canonical
    rw [hv]
    exact (AspisR1.SamplerNatModel.gammaDigits_canonical (AspisR1.SourceSamplerByteRank.rank b)).2
  have hdec := PV_B2_C_ArrayDigits.decode a (PV_B2_C_GammaSource.canonical_array a ha)
  have hout : out = PV_B2_C_ArrayDigits.raw a := by
    exact Result.ok.inj (hd.symm.trans hdec)
  have hold : old = PV_B2_C_ArrayDigits.raw a := by
    change ok (decode a) = ok old at hc
    rw [PV_B2_E_OrdinaryOriginal.decode_eq a (PV_B2_C_GammaSource.canonical_array a ha)] at hc
    exact (Result.ok.inj hc).symm
  rw [PV_B2_C_GammaSource.raw_eq,PV_B2_C_GammaSource.normalized_eq,he]
  change ok out = sample originalOps b
  rw [ho,hout,hold]

open ProverRwFull
variable [ExternalTypes]
def callback (b : Bytes) : Result Native :=
  mapResult toNative (PV_B2_C_249.host_sampler.gamma_sample b)
def selected (ops : ExternalFuns) : ExternalFuns :=
  {PV_B2_E_Install250.selected ops with op249 := callback}
def originalDictionary (ops : ExternalFuns) : ExternalFuns :=
  {PV_B2_E_Install250.originalDictionary ops with
    op249 := fun b => mapResult toNative (originalGamma b)}

theorem selected_callback (ops : ExternalFuns) (b : Bytes) :
    (selected ops).op249 b = mapResult toNative (originalGamma b) := by
  change mapResult toNative _ = _
  rw [copy_equal_original]

theorem gamma_law (ops : ExternalFuns) (b : Bytes) :
    ∃ a : PV_B2_C_GammaNumeric.Digits,
      (selected ops).op249 b = ok (toNative (PV_B2_C_ArrayDigits.raw a)) ∧ Canonical a ∧
      AspisR1.SamplerAddDigits.digitsValue AspisR1.SamplerMachineBounds.P (values a) =
        AspisR1.SourceSamplerByteRank.rank b % (AspisR1.SamplerMachineBounds.P^8-1)+1 ∧
      0 < AspisR1.SamplerAddDigits.digitsValue AspisR1.SamplerMachineBounds.P (values a) ∧
      AspisR1.SamplerAddDigits.digitsValue AspisR1.SamplerMachineBounds.P (values a) <
        AspisR1.SamplerMachineBounds.P^8 := by
  obtain ⟨a,he,hc,hv,hp,hb⟩ := PV_B2_C_GammaSource.op249_source b
  refine ⟨a,?_,hc,hv,hp,hb⟩
  change mapResult toNative _ = _
  rw [he]
  rfl

theorem nonfailure (ops : ExternalFuns) (b : Bytes) :
    ∃ out, (selected ops).op249 b = ok out := by
  obtain ⟨a,h,_,_,_,_⟩ := gamma_law ops b
  exact ⟨_,h⟩
theorem nonvacuity (ops : ExternalFuns) :
    ∃ out, (selected ops).op249 (Array.repeat 32#usize 0#u8) = ok out := nonfailure ops _
theorem ordinary_preserved (ops : ExternalFuns) :
    (selected ops).op250 = (PV_B2_E_Install250.selected ops).op250 := rfl

theorem dictionaries (ops : ExternalFuns) : selected ops = originalDictionary ops := by
  have h : callback = (fun b => mapResult toNative (originalGamma b)) := by
    funext b
    exact selected_callback ops b
  unfold selected originalDictionary
  rw [PV_B2_E_Install250.dictionaries,h]

theorem observations {O : Sort _} (observe : ExternalFuns → O) (ops : ExternalFuns) :
    observe (selected ops) = observe (originalDictionary ops) := congrArg observe (dictionaries ops)
theorem preserved_0 (ops : ExternalFuns) : @ExternalFuns.op0 _ (selected ops) = @ExternalFuns.op0 _ ops := by
  exact PV_B2_E_Install250.preserved_0 ops
theorem preserved_1 (ops : ExternalFuns) : @ExternalFuns.op1 _ (selected ops) = @ExternalFuns.op1 _ ops := by
  exact PV_B2_E_Install250.preserved_1 ops
theorem preserved_2 (ops : ExternalFuns) : @ExternalFuns.op2 _ (selected ops) = @ExternalFuns.op2 _ ops := by
  exact PV_B2_E_Install250.preserved_2 ops
theorem preserved_3 (ops : ExternalFuns) : @ExternalFuns.op3 _ (selected ops) = @ExternalFuns.op3 _ ops := by
  exact PV_B2_E_Install250.preserved_3 ops
theorem preserved_4 (ops : ExternalFuns) : @ExternalFuns.op4 _ (selected ops) = @ExternalFuns.op4 _ ops := by
  exact PV_B2_E_Install250.preserved_4 ops
theorem preserved_5 (ops : ExternalFuns) : @ExternalFuns.op5 _ (selected ops) = @ExternalFuns.op5 _ ops := by
  exact PV_B2_E_Install250.preserved_5 ops
theorem preserved_6 (ops : ExternalFuns) : @ExternalFuns.op6 _ (selected ops) = @ExternalFuns.op6 _ ops := by
  exact PV_B2_E_Install250.preserved_6 ops
theorem preserved_7 (ops : ExternalFuns) : @ExternalFuns.op7 _ (selected ops) = @ExternalFuns.op7 _ ops := by
  exact PV_B2_E_Install250.preserved_7 ops
theorem preserved_8 (ops : ExternalFuns) : @ExternalFuns.op8 _ (selected ops) = @ExternalFuns.op8 _ ops := by
  exact PV_B2_E_Install250.preserved_8 ops
theorem preserved_9 (ops : ExternalFuns) : @ExternalFuns.op9 _ (selected ops) = @ExternalFuns.op9 _ ops := by
  exact PV_B2_E_Install250.preserved_9 ops
theorem preserved_10 (ops : ExternalFuns) : @ExternalFuns.op10 _ (selected ops) = @ExternalFuns.op10 _ ops := by
  exact PV_B2_E_Install250.preserved_10 ops
theorem preserved_11 (ops : ExternalFuns) : @ExternalFuns.op11 _ (selected ops) = @ExternalFuns.op11 _ ops := by
  exact PV_B2_E_Install250.preserved_11 ops
theorem preserved_12 (ops : ExternalFuns) : @ExternalFuns.op12 _ (selected ops) = @ExternalFuns.op12 _ ops := by
  exact PV_B2_E_Install250.preserved_12 ops
theorem preserved_13 (ops : ExternalFuns) : @ExternalFuns.op13 _ (selected ops) = @ExternalFuns.op13 _ ops := by
  exact PV_B2_E_Install250.preserved_13 ops
theorem preserved_14 (ops : ExternalFuns) : @ExternalFuns.op14 _ (selected ops) = @ExternalFuns.op14 _ ops := by
  exact PV_B2_E_Install250.preserved_14 ops
theorem preserved_15 (ops : ExternalFuns) : @ExternalFuns.op15 _ (selected ops) = @ExternalFuns.op15 _ ops := by
  exact PV_B2_E_Install250.preserved_15 ops
theorem preserved_16 (ops : ExternalFuns) : @ExternalFuns.op16 _ (selected ops) = @ExternalFuns.op16 _ ops := by
  exact PV_B2_E_Install250.preserved_16 ops
theorem preserved_17 (ops : ExternalFuns) : @ExternalFuns.op17 _ (selected ops) = @ExternalFuns.op17 _ ops := by
  exact PV_B2_E_Install250.preserved_17 ops
theorem preserved_18 (ops : ExternalFuns) : @ExternalFuns.op18 _ (selected ops) = @ExternalFuns.op18 _ ops := by
  exact PV_B2_E_Install250.preserved_18 ops
theorem preserved_19 (ops : ExternalFuns) : @ExternalFuns.op19 _ (selected ops) = @ExternalFuns.op19 _ ops := by
  exact PV_B2_E_Install250.preserved_19 ops
theorem preserved_20 (ops : ExternalFuns) : @ExternalFuns.op20 _ (selected ops) = @ExternalFuns.op20 _ ops := by
  exact PV_B2_E_Install250.preserved_20 ops
theorem preserved_21 (ops : ExternalFuns) : @ExternalFuns.op21 _ (selected ops) = @ExternalFuns.op21 _ ops := by
  exact PV_B2_E_Install250.preserved_21 ops
theorem preserved_22 (ops : ExternalFuns) : @ExternalFuns.op22 _ (selected ops) = @ExternalFuns.op22 _ ops := by
  exact PV_B2_E_Install250.preserved_22 ops
theorem preserved_23 (ops : ExternalFuns) : @ExternalFuns.op23 _ (selected ops) = @ExternalFuns.op23 _ ops := by
  exact PV_B2_E_Install250.preserved_23 ops
theorem preserved_24 (ops : ExternalFuns) : @ExternalFuns.op24 _ (selected ops) = @ExternalFuns.op24 _ ops := by
  exact PV_B2_E_Install250.preserved_24 ops
theorem preserved_25 (ops : ExternalFuns) : @ExternalFuns.op25 _ (selected ops) = @ExternalFuns.op25 _ ops := by
  exact PV_B2_E_Install250.preserved_25 ops
theorem preserved_26 (ops : ExternalFuns) : @ExternalFuns.op26 _ (selected ops) = @ExternalFuns.op26 _ ops := by
  exact PV_B2_E_Install250.preserved_26 ops
theorem preserved_27 (ops : ExternalFuns) : @ExternalFuns.op27 _ (selected ops) = @ExternalFuns.op27 _ ops := by
  exact PV_B2_E_Install250.preserved_27 ops
theorem preserved_28 (ops : ExternalFuns) : @ExternalFuns.op28 _ (selected ops) = @ExternalFuns.op28 _ ops := by
  exact PV_B2_E_Install250.preserved_28 ops
theorem preserved_29 (ops : ExternalFuns) : @ExternalFuns.op29 _ (selected ops) = @ExternalFuns.op29 _ ops := by
  exact PV_B2_E_Install250.preserved_29 ops
theorem preserved_30 (ops : ExternalFuns) : @ExternalFuns.op30 _ (selected ops) = @ExternalFuns.op30 _ ops := by
  exact PV_B2_E_Install250.preserved_30 ops
theorem preserved_31 (ops : ExternalFuns) : @ExternalFuns.op31 _ (selected ops) = @ExternalFuns.op31 _ ops := by
  exact PV_B2_E_Install250.preserved_31 ops
theorem preserved_32 (ops : ExternalFuns) : @ExternalFuns.op32 _ (selected ops) = @ExternalFuns.op32 _ ops := by
  exact PV_B2_E_Install250.preserved_32 ops
theorem preserved_33 (ops : ExternalFuns) : @ExternalFuns.op33 _ (selected ops) = @ExternalFuns.op33 _ ops := by
  exact PV_B2_E_Install250.preserved_33 ops
theorem preserved_34 (ops : ExternalFuns) : @ExternalFuns.op34 _ (selected ops) = @ExternalFuns.op34 _ ops := by
  exact PV_B2_E_Install250.preserved_34 ops
theorem preserved_35 (ops : ExternalFuns) : @ExternalFuns.op35 _ (selected ops) = @ExternalFuns.op35 _ ops := by
  exact PV_B2_E_Install250.preserved_35 ops
theorem preserved_36 (ops : ExternalFuns) : @ExternalFuns.op36 _ (selected ops) = @ExternalFuns.op36 _ ops := by
  exact PV_B2_E_Install250.preserved_36 ops
theorem preserved_37 (ops : ExternalFuns) : @ExternalFuns.op37 _ (selected ops) = @ExternalFuns.op37 _ ops := by
  exact PV_B2_E_Install250.preserved_37 ops
theorem preserved_38 (ops : ExternalFuns) : @ExternalFuns.op38 _ (selected ops) = @ExternalFuns.op38 _ ops := by
  exact PV_B2_E_Install250.preserved_38 ops
theorem preserved_39 (ops : ExternalFuns) : @ExternalFuns.op39 _ (selected ops) = @ExternalFuns.op39 _ ops := by
  exact PV_B2_E_Install250.preserved_39 ops
theorem preserved_40 (ops : ExternalFuns) : @ExternalFuns.op40 _ (selected ops) = @ExternalFuns.op40 _ ops := by
  exact PV_B2_E_Install250.preserved_40 ops
theorem preserved_41 (ops : ExternalFuns) : @ExternalFuns.op41 _ (selected ops) = @ExternalFuns.op41 _ ops := by
  exact PV_B2_E_Install250.preserved_41 ops
theorem preserved_42 (ops : ExternalFuns) : @ExternalFuns.op42 _ (selected ops) = @ExternalFuns.op42 _ ops := by
  exact PV_B2_E_Install250.preserved_42 ops
theorem preserved_43 (ops : ExternalFuns) : @ExternalFuns.op43 _ (selected ops) = @ExternalFuns.op43 _ ops := by
  exact PV_B2_E_Install250.preserved_43 ops
theorem preserved_44 (ops : ExternalFuns) : @ExternalFuns.op44 _ (selected ops) = @ExternalFuns.op44 _ ops := by
  exact PV_B2_E_Install250.preserved_44 ops
theorem preserved_45 (ops : ExternalFuns) : @ExternalFuns.op45 _ (selected ops) = @ExternalFuns.op45 _ ops := by
  exact PV_B2_E_Install250.preserved_45 ops
theorem preserved_46 (ops : ExternalFuns) : @ExternalFuns.op46 _ (selected ops) = @ExternalFuns.op46 _ ops := by
  exact PV_B2_E_Install250.preserved_46 ops
theorem preserved_47 (ops : ExternalFuns) : @ExternalFuns.op47 _ (selected ops) = @ExternalFuns.op47 _ ops := by
  exact PV_B2_E_Install250.preserved_47 ops
theorem preserved_48 (ops : ExternalFuns) : @ExternalFuns.op48 _ (selected ops) = @ExternalFuns.op48 _ ops := by
  exact PV_B2_E_Install250.preserved_48 ops
theorem preserved_49 (ops : ExternalFuns) : @ExternalFuns.op49 _ (selected ops) = @ExternalFuns.op49 _ ops := by
  exact PV_B2_E_Install250.preserved_49 ops
theorem preserved_50 (ops : ExternalFuns) : @ExternalFuns.op50 _ (selected ops) = @ExternalFuns.op50 _ ops := by
  exact PV_B2_E_Install250.preserved_50 ops
theorem preserved_51 (ops : ExternalFuns) : @ExternalFuns.op51 _ (selected ops) = @ExternalFuns.op51 _ ops := by
  exact PV_B2_E_Install250.preserved_51 ops
theorem preserved_52 (ops : ExternalFuns) : @ExternalFuns.op52 _ (selected ops) = @ExternalFuns.op52 _ ops := by
  exact PV_B2_E_Install250.preserved_52 ops
theorem preserved_53 (ops : ExternalFuns) : @ExternalFuns.op53 _ (selected ops) = @ExternalFuns.op53 _ ops := by
  exact PV_B2_E_Install250.preserved_53 ops
theorem preserved_54 (ops : ExternalFuns) : @ExternalFuns.op54 _ (selected ops) = @ExternalFuns.op54 _ ops := by
  exact PV_B2_E_Install250.preserved_54 ops
theorem preserved_55 (ops : ExternalFuns) : @ExternalFuns.op55 _ (selected ops) = @ExternalFuns.op55 _ ops := by
  exact PV_B2_E_Install250.preserved_55 ops
theorem preserved_56 (ops : ExternalFuns) : @ExternalFuns.op56 _ (selected ops) = @ExternalFuns.op56 _ ops := by
  exact PV_B2_E_Install250.preserved_56 ops
theorem preserved_57 (ops : ExternalFuns) : @ExternalFuns.op57 _ (selected ops) = @ExternalFuns.op57 _ ops := by
  exact PV_B2_E_Install250.preserved_57 ops
theorem preserved_58 (ops : ExternalFuns) : @ExternalFuns.op58 _ (selected ops) = @ExternalFuns.op58 _ ops := by
  exact PV_B2_E_Install250.preserved_58 ops
theorem preserved_59 (ops : ExternalFuns) : @ExternalFuns.op59 _ (selected ops) = @ExternalFuns.op59 _ ops := by
  exact PV_B2_E_Install250.preserved_59 ops
theorem preserved_60 (ops : ExternalFuns) : @ExternalFuns.op60 _ (selected ops) = @ExternalFuns.op60 _ ops := by
  exact PV_B2_E_Install250.preserved_60 ops
theorem preserved_61 (ops : ExternalFuns) : @ExternalFuns.op61 _ (selected ops) = @ExternalFuns.op61 _ ops := by
  exact PV_B2_E_Install250.preserved_61 ops
theorem preserved_62 (ops : ExternalFuns) : @ExternalFuns.op62 _ (selected ops) = @ExternalFuns.op62 _ ops := by
  exact PV_B2_E_Install250.preserved_62 ops
theorem preserved_63 (ops : ExternalFuns) : @ExternalFuns.op63 _ (selected ops) = @ExternalFuns.op63 _ ops := by
  exact PV_B2_E_Install250.preserved_63 ops
theorem preserved_64 (ops : ExternalFuns) : @ExternalFuns.op64 _ (selected ops) = @ExternalFuns.op64 _ ops := by
  exact PV_B2_E_Install250.preserved_64 ops
theorem preserved_65 (ops : ExternalFuns) : @ExternalFuns.op65 _ (selected ops) = @ExternalFuns.op65 _ ops := by
  exact PV_B2_E_Install250.preserved_65 ops
theorem preserved_66 (ops : ExternalFuns) : @ExternalFuns.op66 _ (selected ops) = @ExternalFuns.op66 _ ops := by
  exact PV_B2_E_Install250.preserved_66 ops
theorem preserved_67 (ops : ExternalFuns) : @ExternalFuns.op67 _ (selected ops) = @ExternalFuns.op67 _ ops := by
  exact PV_B2_E_Install250.preserved_67 ops
theorem preserved_68 (ops : ExternalFuns) : @ExternalFuns.op68 _ (selected ops) = @ExternalFuns.op68 _ ops := by
  exact PV_B2_E_Install250.preserved_68 ops
theorem preserved_69 (ops : ExternalFuns) : @ExternalFuns.op69 _ (selected ops) = @ExternalFuns.op69 _ ops := by
  exact PV_B2_E_Install250.preserved_69 ops
theorem preserved_70 (ops : ExternalFuns) : @ExternalFuns.op70 _ (selected ops) = @ExternalFuns.op70 _ ops := by
  exact PV_B2_E_Install250.preserved_70 ops
theorem preserved_71 (ops : ExternalFuns) : @ExternalFuns.op71 _ (selected ops) = @ExternalFuns.op71 _ ops := by
  exact PV_B2_E_Install250.preserved_71 ops
theorem preserved_72 (ops : ExternalFuns) : @ExternalFuns.op72 _ (selected ops) = @ExternalFuns.op72 _ ops := by
  exact PV_B2_E_Install250.preserved_72 ops
theorem preserved_73 (ops : ExternalFuns) : @ExternalFuns.op73 _ (selected ops) = @ExternalFuns.op73 _ ops := by
  exact PV_B2_E_Install250.preserved_73 ops
theorem preserved_74 (ops : ExternalFuns) : @ExternalFuns.op74 _ (selected ops) = @ExternalFuns.op74 _ ops := by
  exact PV_B2_E_Install250.preserved_74 ops
theorem preserved_75 (ops : ExternalFuns) : @ExternalFuns.op75 _ (selected ops) = @ExternalFuns.op75 _ ops := by
  exact PV_B2_E_Install250.preserved_75 ops
theorem preserved_76 (ops : ExternalFuns) : @ExternalFuns.op76 _ (selected ops) = @ExternalFuns.op76 _ ops := by
  exact PV_B2_E_Install250.preserved_76 ops
theorem preserved_77 (ops : ExternalFuns) : @ExternalFuns.op77 _ (selected ops) = @ExternalFuns.op77 _ ops := by
  exact PV_B2_E_Install250.preserved_77 ops
theorem preserved_78 (ops : ExternalFuns) : @ExternalFuns.op78 _ (selected ops) = @ExternalFuns.op78 _ ops := by
  exact PV_B2_E_Install250.preserved_78 ops
theorem preserved_79 (ops : ExternalFuns) : @ExternalFuns.op79 _ (selected ops) = @ExternalFuns.op79 _ ops := by
  exact PV_B2_E_Install250.preserved_79 ops
theorem preserved_80 (ops : ExternalFuns) : @ExternalFuns.op80 _ (selected ops) = @ExternalFuns.op80 _ ops := by
  exact PV_B2_E_Install250.preserved_80 ops
theorem preserved_81 (ops : ExternalFuns) : @ExternalFuns.op81 _ (selected ops) = @ExternalFuns.op81 _ ops := by
  exact PV_B2_E_Install250.preserved_81 ops
theorem preserved_82 (ops : ExternalFuns) : @ExternalFuns.op82 _ (selected ops) = @ExternalFuns.op82 _ ops := by
  exact PV_B2_E_Install250.preserved_82 ops
theorem preserved_83 (ops : ExternalFuns) : @ExternalFuns.op83 _ (selected ops) = @ExternalFuns.op83 _ ops := by
  exact PV_B2_E_Install250.preserved_83 ops
theorem preserved_84 (ops : ExternalFuns) : @ExternalFuns.op84 _ (selected ops) = @ExternalFuns.op84 _ ops := by
  exact PV_B2_E_Install250.preserved_84 ops
theorem preserved_85 (ops : ExternalFuns) : @ExternalFuns.op85 _ (selected ops) = @ExternalFuns.op85 _ ops := by
  exact PV_B2_E_Install250.preserved_85 ops
theorem preserved_86 (ops : ExternalFuns) : @ExternalFuns.op86 _ (selected ops) = @ExternalFuns.op86 _ ops := by
  exact PV_B2_E_Install250.preserved_86 ops
theorem preserved_87 (ops : ExternalFuns) : @ExternalFuns.op87 _ (selected ops) = @ExternalFuns.op87 _ ops := by
  exact PV_B2_E_Install250.preserved_87 ops
theorem preserved_88 (ops : ExternalFuns) : @ExternalFuns.op88 _ (selected ops) = @ExternalFuns.op88 _ ops := by
  exact PV_B2_E_Install250.preserved_88 ops
theorem preserved_89 (ops : ExternalFuns) : @ExternalFuns.op89 _ (selected ops) = @ExternalFuns.op89 _ ops := by
  exact PV_B2_E_Install250.preserved_89 ops
theorem preserved_90 (ops : ExternalFuns) : @ExternalFuns.op90 _ (selected ops) = @ExternalFuns.op90 _ ops := by
  exact PV_B2_E_Install250.preserved_90 ops
theorem preserved_91 (ops : ExternalFuns) : @ExternalFuns.op91 _ (selected ops) = @ExternalFuns.op91 _ ops := by
  exact PV_B2_E_Install250.preserved_91 ops
theorem preserved_92 (ops : ExternalFuns) : @ExternalFuns.op92 _ (selected ops) = @ExternalFuns.op92 _ ops := by
  exact PV_B2_E_Install250.preserved_92 ops
theorem preserved_93 (ops : ExternalFuns) : @ExternalFuns.op93 _ (selected ops) = @ExternalFuns.op93 _ ops := by
  exact PV_B2_E_Install250.preserved_93 ops
theorem preserved_94 (ops : ExternalFuns) : @ExternalFuns.op94 _ (selected ops) = @ExternalFuns.op94 _ ops := by
  exact PV_B2_E_Install250.preserved_94 ops
theorem preserved_95 (ops : ExternalFuns) : @ExternalFuns.op95 _ (selected ops) = @ExternalFuns.op95 _ ops := by
  exact PV_B2_E_Install250.preserved_95 ops
theorem preserved_96 (ops : ExternalFuns) : @ExternalFuns.op96 _ (selected ops) = @ExternalFuns.op96 _ ops := by
  exact PV_B2_E_Install250.preserved_96 ops
theorem preserved_97 (ops : ExternalFuns) : @ExternalFuns.op97 _ (selected ops) = @ExternalFuns.op97 _ ops := by
  exact PV_B2_E_Install250.preserved_97 ops
theorem preserved_98 (ops : ExternalFuns) : @ExternalFuns.op98 _ (selected ops) = @ExternalFuns.op98 _ ops := by
  exact PV_B2_E_Install250.preserved_98 ops
theorem preserved_99 (ops : ExternalFuns) : @ExternalFuns.op99 _ (selected ops) = @ExternalFuns.op99 _ ops := by
  exact PV_B2_E_Install250.preserved_99 ops
theorem preserved_100 (ops : ExternalFuns) : @ExternalFuns.op100 _ (selected ops) = @ExternalFuns.op100 _ ops := by
  exact PV_B2_E_Install250.preserved_100 ops
theorem preserved_101 (ops : ExternalFuns) : @ExternalFuns.op101 _ (selected ops) = @ExternalFuns.op101 _ ops := by
  exact PV_B2_E_Install250.preserved_101 ops
theorem preserved_102 (ops : ExternalFuns) : @ExternalFuns.op102 _ (selected ops) = @ExternalFuns.op102 _ ops := by
  exact PV_B2_E_Install250.preserved_102 ops
theorem preserved_103 (ops : ExternalFuns) : @ExternalFuns.op103 _ (selected ops) = @ExternalFuns.op103 _ ops := by
  exact PV_B2_E_Install250.preserved_103 ops
theorem preserved_104 (ops : ExternalFuns) : @ExternalFuns.op104 _ (selected ops) = @ExternalFuns.op104 _ ops := by
  exact PV_B2_E_Install250.preserved_104 ops
theorem preserved_105 (ops : ExternalFuns) : @ExternalFuns.op105 _ (selected ops) = @ExternalFuns.op105 _ ops := by
  exact PV_B2_E_Install250.preserved_105 ops
theorem preserved_106 (ops : ExternalFuns) : @ExternalFuns.op106 _ (selected ops) = @ExternalFuns.op106 _ ops := by
  exact PV_B2_E_Install250.preserved_106 ops
theorem preserved_107 (ops : ExternalFuns) : @ExternalFuns.op107 _ (selected ops) = @ExternalFuns.op107 _ ops := by
  exact PV_B2_E_Install250.preserved_107 ops
theorem preserved_108 (ops : ExternalFuns) : @ExternalFuns.op108 _ (selected ops) = @ExternalFuns.op108 _ ops := by
  exact PV_B2_E_Install250.preserved_108 ops
theorem preserved_109 (ops : ExternalFuns) : @ExternalFuns.op109 _ (selected ops) = @ExternalFuns.op109 _ ops := by
  exact PV_B2_E_Install250.preserved_109 ops
theorem preserved_110 (ops : ExternalFuns) : @ExternalFuns.op110 _ (selected ops) = @ExternalFuns.op110 _ ops := by
  exact PV_B2_E_Install250.preserved_110 ops
theorem preserved_111 (ops : ExternalFuns) : @ExternalFuns.op111 _ (selected ops) = @ExternalFuns.op111 _ ops := by
  exact PV_B2_E_Install250.preserved_111 ops
theorem preserved_112 (ops : ExternalFuns) : @ExternalFuns.op112 _ (selected ops) = @ExternalFuns.op112 _ ops := by
  exact PV_B2_E_Install250.preserved_112 ops
theorem preserved_113 (ops : ExternalFuns) : @ExternalFuns.op113 _ (selected ops) = @ExternalFuns.op113 _ ops := by
  exact PV_B2_E_Install250.preserved_113 ops
theorem preserved_114 (ops : ExternalFuns) : @ExternalFuns.op114 _ (selected ops) = @ExternalFuns.op114 _ ops := by
  exact PV_B2_E_Install250.preserved_114 ops
theorem preserved_115 (ops : ExternalFuns) : @ExternalFuns.op115 _ (selected ops) = @ExternalFuns.op115 _ ops := by
  exact PV_B2_E_Install250.preserved_115 ops
theorem preserved_116 (ops : ExternalFuns) : @ExternalFuns.op116 _ (selected ops) = @ExternalFuns.op116 _ ops := by
  exact PV_B2_E_Install250.preserved_116 ops
theorem preserved_117 (ops : ExternalFuns) : @ExternalFuns.op117 _ (selected ops) = @ExternalFuns.op117 _ ops := by
  exact PV_B2_E_Install250.preserved_117 ops
theorem preserved_118 (ops : ExternalFuns) : @ExternalFuns.op118 _ (selected ops) = @ExternalFuns.op118 _ ops := by
  exact PV_B2_E_Install250.preserved_118 ops
theorem preserved_119 (ops : ExternalFuns) : @ExternalFuns.op119 _ (selected ops) = @ExternalFuns.op119 _ ops := by
  exact PV_B2_E_Install250.preserved_119 ops
theorem preserved_120 (ops : ExternalFuns) : @ExternalFuns.op120 _ (selected ops) = @ExternalFuns.op120 _ ops := by
  exact PV_B2_E_Install250.preserved_120 ops
theorem preserved_121 (ops : ExternalFuns) : @ExternalFuns.op121 _ (selected ops) = @ExternalFuns.op121 _ ops := by
  exact PV_B2_E_Install250.preserved_121 ops
theorem preserved_122 (ops : ExternalFuns) : @ExternalFuns.op122 _ (selected ops) = @ExternalFuns.op122 _ ops := by
  exact PV_B2_E_Install250.preserved_122 ops
theorem preserved_123 (ops : ExternalFuns) : @ExternalFuns.op123 _ (selected ops) = @ExternalFuns.op123 _ ops := by
  exact PV_B2_E_Install250.preserved_123 ops
theorem preserved_124 (ops : ExternalFuns) : @ExternalFuns.op124 _ (selected ops) = @ExternalFuns.op124 _ ops := by
  exact PV_B2_E_Install250.preserved_124 ops
theorem preserved_125 (ops : ExternalFuns) : @ExternalFuns.op125 _ (selected ops) = @ExternalFuns.op125 _ ops := by
  exact PV_B2_E_Install250.preserved_125 ops
theorem preserved_126 (ops : ExternalFuns) : @ExternalFuns.op126 _ (selected ops) = @ExternalFuns.op126 _ ops := by
  exact PV_B2_E_Install250.preserved_126 ops
theorem preserved_127 (ops : ExternalFuns) : @ExternalFuns.op127 _ (selected ops) = @ExternalFuns.op127 _ ops := by
  exact PV_B2_E_Install250.preserved_127 ops
theorem preserved_128 (ops : ExternalFuns) : @ExternalFuns.op128 _ (selected ops) = @ExternalFuns.op128 _ ops := by
  exact PV_B2_E_Install250.preserved_128 ops
theorem preserved_129 (ops : ExternalFuns) : @ExternalFuns.op129 _ (selected ops) = @ExternalFuns.op129 _ ops := by
  exact PV_B2_E_Install250.preserved_129 ops
theorem preserved_130 (ops : ExternalFuns) : @ExternalFuns.op130 _ (selected ops) = @ExternalFuns.op130 _ ops := by
  exact PV_B2_E_Install250.preserved_130 ops
theorem preserved_131 (ops : ExternalFuns) : @ExternalFuns.op131 _ (selected ops) = @ExternalFuns.op131 _ ops := by
  exact PV_B2_E_Install250.preserved_131 ops
theorem preserved_132 (ops : ExternalFuns) : @ExternalFuns.op132 _ (selected ops) = @ExternalFuns.op132 _ ops := by
  exact PV_B2_E_Install250.preserved_132 ops
theorem preserved_133 (ops : ExternalFuns) : @ExternalFuns.op133 _ (selected ops) = @ExternalFuns.op133 _ ops := by
  exact PV_B2_E_Install250.preserved_133 ops
theorem preserved_134 (ops : ExternalFuns) : @ExternalFuns.op134 _ (selected ops) = @ExternalFuns.op134 _ ops := by
  exact PV_B2_E_Install250.preserved_134 ops
theorem preserved_135 (ops : ExternalFuns) : @ExternalFuns.op135 _ (selected ops) = @ExternalFuns.op135 _ ops := by
  exact PV_B2_E_Install250.preserved_135 ops
theorem preserved_136 (ops : ExternalFuns) : @ExternalFuns.op136 _ (selected ops) = @ExternalFuns.op136 _ ops := by
  exact PV_B2_E_Install250.preserved_136 ops
theorem preserved_137 (ops : ExternalFuns) : @ExternalFuns.op137 _ (selected ops) = @ExternalFuns.op137 _ ops := by
  exact PV_B2_E_Install250.preserved_137 ops
theorem preserved_138 (ops : ExternalFuns) : @ExternalFuns.op138 _ (selected ops) = @ExternalFuns.op138 _ ops := by
  exact PV_B2_E_Install250.preserved_138 ops
theorem preserved_139 (ops : ExternalFuns) : @ExternalFuns.op139 _ (selected ops) = @ExternalFuns.op139 _ ops := by
  exact PV_B2_E_Install250.preserved_139 ops
theorem preserved_140 (ops : ExternalFuns) : @ExternalFuns.op140 _ (selected ops) = @ExternalFuns.op140 _ ops := by
  exact PV_B2_E_Install250.preserved_140 ops
theorem preserved_141 (ops : ExternalFuns) : @ExternalFuns.op141 _ (selected ops) = @ExternalFuns.op141 _ ops := by
  exact PV_B2_E_Install250.preserved_141 ops
theorem preserved_142 (ops : ExternalFuns) : @ExternalFuns.op142 _ (selected ops) = @ExternalFuns.op142 _ ops := by
  exact PV_B2_E_Install250.preserved_142 ops
theorem preserved_143 (ops : ExternalFuns) : @ExternalFuns.op143 _ (selected ops) = @ExternalFuns.op143 _ ops := by
  exact PV_B2_E_Install250.preserved_143 ops
theorem preserved_144 (ops : ExternalFuns) : @ExternalFuns.op144 _ (selected ops) = @ExternalFuns.op144 _ ops := by
  exact PV_B2_E_Install250.preserved_144 ops
theorem preserved_145 (ops : ExternalFuns) : @ExternalFuns.op145 _ (selected ops) = @ExternalFuns.op145 _ ops := by
  exact PV_B2_E_Install250.preserved_145 ops
theorem preserved_146 (ops : ExternalFuns) : @ExternalFuns.op146 _ (selected ops) = @ExternalFuns.op146 _ ops := by
  exact PV_B2_E_Install250.preserved_146 ops
theorem preserved_147 (ops : ExternalFuns) : @ExternalFuns.op147 _ (selected ops) = @ExternalFuns.op147 _ ops := by
  exact PV_B2_E_Install250.preserved_147 ops
theorem preserved_148 (ops : ExternalFuns) : @ExternalFuns.op148 _ (selected ops) = @ExternalFuns.op148 _ ops := by
  exact PV_B2_E_Install250.preserved_148 ops
theorem preserved_149 (ops : ExternalFuns) : @ExternalFuns.op149 _ (selected ops) = @ExternalFuns.op149 _ ops := by
  exact PV_B2_E_Install250.preserved_149 ops
theorem preserved_150 (ops : ExternalFuns) : @ExternalFuns.op150 _ (selected ops) = @ExternalFuns.op150 _ ops := by
  exact PV_B2_E_Install250.preserved_150 ops
theorem preserved_151 (ops : ExternalFuns) : @ExternalFuns.op151 _ (selected ops) = @ExternalFuns.op151 _ ops := by
  exact PV_B2_E_Install250.preserved_151 ops
theorem preserved_152 (ops : ExternalFuns) : @ExternalFuns.op152 _ (selected ops) = @ExternalFuns.op152 _ ops := by
  exact PV_B2_E_Install250.preserved_152 ops
theorem preserved_153 (ops : ExternalFuns) : @ExternalFuns.op153 _ (selected ops) = @ExternalFuns.op153 _ ops := by
  exact PV_B2_E_Install250.preserved_153 ops
theorem preserved_154 (ops : ExternalFuns) : @ExternalFuns.op154 _ (selected ops) = @ExternalFuns.op154 _ ops := by
  exact PV_B2_E_Install250.preserved_154 ops
theorem preserved_155 (ops : ExternalFuns) : @ExternalFuns.op155 _ (selected ops) = @ExternalFuns.op155 _ ops := by
  exact PV_B2_E_Install250.preserved_155 ops
theorem preserved_156 (ops : ExternalFuns) : @ExternalFuns.op156 _ (selected ops) = @ExternalFuns.op156 _ ops := by
  exact PV_B2_E_Install250.preserved_156 ops
theorem preserved_157 (ops : ExternalFuns) : @ExternalFuns.op157 _ (selected ops) = @ExternalFuns.op157 _ ops := by
  exact PV_B2_E_Install250.preserved_157 ops
theorem preserved_158 (ops : ExternalFuns) : @ExternalFuns.op158 _ (selected ops) = @ExternalFuns.op158 _ ops := by
  exact PV_B2_E_Install250.preserved_158 ops
theorem preserved_159 (ops : ExternalFuns) : @ExternalFuns.op159 _ (selected ops) = @ExternalFuns.op159 _ ops := by
  exact PV_B2_E_Install250.preserved_159 ops
theorem preserved_160 (ops : ExternalFuns) : @ExternalFuns.op160 _ (selected ops) = @ExternalFuns.op160 _ ops := by
  exact PV_B2_E_Install250.preserved_160 ops
theorem preserved_161 (ops : ExternalFuns) : @ExternalFuns.op161 _ (selected ops) = @ExternalFuns.op161 _ ops := by
  exact PV_B2_E_Install250.preserved_161 ops
theorem preserved_162 (ops : ExternalFuns) : @ExternalFuns.op162 _ (selected ops) = @ExternalFuns.op162 _ ops := by
  exact PV_B2_E_Install250.preserved_162 ops
theorem preserved_163 (ops : ExternalFuns) : @ExternalFuns.op163 _ (selected ops) = @ExternalFuns.op163 _ ops := by
  exact PV_B2_E_Install250.preserved_163 ops
theorem preserved_164 (ops : ExternalFuns) : @ExternalFuns.op164 _ (selected ops) = @ExternalFuns.op164 _ ops := by
  exact PV_B2_E_Install250.preserved_164 ops
theorem preserved_165 (ops : ExternalFuns) : @ExternalFuns.op165 _ (selected ops) = @ExternalFuns.op165 _ ops := by
  exact PV_B2_E_Install250.preserved_165 ops
theorem preserved_166 (ops : ExternalFuns) : @ExternalFuns.op166 _ (selected ops) = @ExternalFuns.op166 _ ops := by
  exact PV_B2_E_Install250.preserved_166 ops
theorem preserved_167 (ops : ExternalFuns) : @ExternalFuns.op167 _ (selected ops) = @ExternalFuns.op167 _ ops := by
  exact PV_B2_E_Install250.preserved_167 ops
theorem preserved_168 (ops : ExternalFuns) : @ExternalFuns.op168 _ (selected ops) = @ExternalFuns.op168 _ ops := by
  exact PV_B2_E_Install250.preserved_168 ops
theorem preserved_169 (ops : ExternalFuns) : @ExternalFuns.op169 _ (selected ops) = @ExternalFuns.op169 _ ops := by
  exact PV_B2_E_Install250.preserved_169 ops
theorem preserved_170 (ops : ExternalFuns) : @ExternalFuns.op170 _ (selected ops) = @ExternalFuns.op170 _ ops := by
  exact PV_B2_E_Install250.preserved_170 ops
theorem preserved_171 (ops : ExternalFuns) : @ExternalFuns.op171 _ (selected ops) = @ExternalFuns.op171 _ ops := by
  exact PV_B2_E_Install250.preserved_171 ops
theorem preserved_172 (ops : ExternalFuns) : @ExternalFuns.op172 _ (selected ops) = @ExternalFuns.op172 _ ops := by
  exact PV_B2_E_Install250.preserved_172 ops
theorem preserved_173 (ops : ExternalFuns) : @ExternalFuns.op173 _ (selected ops) = @ExternalFuns.op173 _ ops := by
  exact PV_B2_E_Install250.preserved_173 ops
theorem preserved_174 (ops : ExternalFuns) : @ExternalFuns.op174 _ (selected ops) = @ExternalFuns.op174 _ ops := by
  exact PV_B2_E_Install250.preserved_174 ops
theorem preserved_175 (ops : ExternalFuns) : @ExternalFuns.op175 _ (selected ops) = @ExternalFuns.op175 _ ops := by
  exact PV_B2_E_Install250.preserved_175 ops
theorem preserved_176 (ops : ExternalFuns) : @ExternalFuns.op176 _ (selected ops) = @ExternalFuns.op176 _ ops := by
  exact PV_B2_E_Install250.preserved_176 ops
theorem preserved_177 (ops : ExternalFuns) : @ExternalFuns.op177 _ (selected ops) = @ExternalFuns.op177 _ ops := by
  exact PV_B2_E_Install250.preserved_177 ops
theorem preserved_178 (ops : ExternalFuns) : @ExternalFuns.op178 _ (selected ops) = @ExternalFuns.op178 _ ops := by
  exact PV_B2_E_Install250.preserved_178 ops
theorem preserved_179 (ops : ExternalFuns) : @ExternalFuns.op179 _ (selected ops) = @ExternalFuns.op179 _ ops := by
  exact PV_B2_E_Install250.preserved_179 ops
theorem preserved_180 (ops : ExternalFuns) : @ExternalFuns.op180 _ (selected ops) = @ExternalFuns.op180 _ ops := by
  exact PV_B2_E_Install250.preserved_180 ops
theorem preserved_181 (ops : ExternalFuns) : @ExternalFuns.op181 _ (selected ops) = @ExternalFuns.op181 _ ops := by
  exact PV_B2_E_Install250.preserved_181 ops
theorem preserved_182 (ops : ExternalFuns) : @ExternalFuns.op182 _ (selected ops) = @ExternalFuns.op182 _ ops := by
  exact PV_B2_E_Install250.preserved_182 ops
theorem preserved_183 (ops : ExternalFuns) : @ExternalFuns.op183 _ (selected ops) = @ExternalFuns.op183 _ ops := by
  exact PV_B2_E_Install250.preserved_183 ops
theorem preserved_184 (ops : ExternalFuns) : @ExternalFuns.op184 _ (selected ops) = @ExternalFuns.op184 _ ops := by
  exact PV_B2_E_Install250.preserved_184 ops
theorem preserved_185 (ops : ExternalFuns) : @ExternalFuns.op185 _ (selected ops) = @ExternalFuns.op185 _ ops := by
  exact PV_B2_E_Install250.preserved_185 ops
theorem preserved_186 (ops : ExternalFuns) : @ExternalFuns.op186 _ (selected ops) = @ExternalFuns.op186 _ ops := by
  exact PV_B2_E_Install250.preserved_186 ops
theorem preserved_187 (ops : ExternalFuns) : @ExternalFuns.op187 _ (selected ops) = @ExternalFuns.op187 _ ops := by
  exact PV_B2_E_Install250.preserved_187 ops
theorem preserved_188 (ops : ExternalFuns) : @ExternalFuns.op188 _ (selected ops) = @ExternalFuns.op188 _ ops := by
  exact PV_B2_E_Install250.preserved_188 ops
theorem preserved_189 (ops : ExternalFuns) : @ExternalFuns.op189 _ (selected ops) = @ExternalFuns.op189 _ ops := by
  exact PV_B2_E_Install250.preserved_189 ops
theorem preserved_190 (ops : ExternalFuns) : @ExternalFuns.op190 _ (selected ops) = @ExternalFuns.op190 _ ops := by
  exact PV_B2_E_Install250.preserved_190 ops
theorem preserved_191 (ops : ExternalFuns) : @ExternalFuns.op191 _ (selected ops) = @ExternalFuns.op191 _ ops := by
  exact PV_B2_E_Install250.preserved_191 ops
theorem preserved_192 (ops : ExternalFuns) : @ExternalFuns.op192 _ (selected ops) = @ExternalFuns.op192 _ ops := by
  exact PV_B2_E_Install250.preserved_192 ops
theorem preserved_193 (ops : ExternalFuns) : @ExternalFuns.op193 _ (selected ops) = @ExternalFuns.op193 _ ops := by
  exact PV_B2_E_Install250.preserved_193 ops
theorem preserved_194 (ops : ExternalFuns) : @ExternalFuns.op194 _ (selected ops) = @ExternalFuns.op194 _ ops := by
  exact PV_B2_E_Install250.preserved_194 ops
theorem preserved_195 (ops : ExternalFuns) : @ExternalFuns.op195 _ (selected ops) = @ExternalFuns.op195 _ ops := by
  exact PV_B2_E_Install250.preserved_195 ops
theorem preserved_196 (ops : ExternalFuns) : @ExternalFuns.op196 _ (selected ops) = @ExternalFuns.op196 _ ops := by
  exact PV_B2_E_Install250.preserved_196 ops
theorem preserved_197 (ops : ExternalFuns) : @ExternalFuns.op197 _ (selected ops) = @ExternalFuns.op197 _ ops := by
  exact PV_B2_E_Install250.preserved_197 ops
theorem preserved_198 (ops : ExternalFuns) : @ExternalFuns.op198 _ (selected ops) = @ExternalFuns.op198 _ ops := by
  exact PV_B2_E_Install250.preserved_198 ops
theorem preserved_199 (ops : ExternalFuns) : @ExternalFuns.op199 _ (selected ops) = @ExternalFuns.op199 _ ops := by
  exact PV_B2_E_Install250.preserved_199 ops
theorem preserved_200 (ops : ExternalFuns) : @ExternalFuns.op200 _ (selected ops) = @ExternalFuns.op200 _ ops := by
  exact PV_B2_E_Install250.preserved_200 ops
theorem preserved_201 (ops : ExternalFuns) : @ExternalFuns.op201 _ (selected ops) = @ExternalFuns.op201 _ ops := by
  exact PV_B2_E_Install250.preserved_201 ops
theorem preserved_202 (ops : ExternalFuns) : @ExternalFuns.op202 _ (selected ops) = @ExternalFuns.op202 _ ops := by
  exact PV_B2_E_Install250.preserved_202 ops
theorem preserved_203 (ops : ExternalFuns) : @ExternalFuns.op203 _ (selected ops) = @ExternalFuns.op203 _ ops := by
  exact PV_B2_E_Install250.preserved_203 ops
theorem preserved_204 (ops : ExternalFuns) : @ExternalFuns.op204 _ (selected ops) = @ExternalFuns.op204 _ ops := by
  exact PV_B2_E_Install250.preserved_204 ops
theorem preserved_205 (ops : ExternalFuns) : @ExternalFuns.op205 _ (selected ops) = @ExternalFuns.op205 _ ops := by
  exact PV_B2_E_Install250.preserved_205 ops
theorem preserved_206 (ops : ExternalFuns) : @ExternalFuns.op206 _ (selected ops) = @ExternalFuns.op206 _ ops := by
  exact PV_B2_E_Install250.preserved_206 ops
theorem preserved_207 (ops : ExternalFuns) : @ExternalFuns.op207 _ (selected ops) = @ExternalFuns.op207 _ ops := by
  exact PV_B2_E_Install250.preserved_207 ops
theorem preserved_208 (ops : ExternalFuns) : @ExternalFuns.op208 _ (selected ops) = @ExternalFuns.op208 _ ops := by
  exact PV_B2_E_Install250.preserved_208 ops
theorem preserved_209 (ops : ExternalFuns) : @ExternalFuns.op209 _ (selected ops) = @ExternalFuns.op209 _ ops := by
  exact PV_B2_E_Install250.preserved_209 ops
theorem preserved_210 (ops : ExternalFuns) : @ExternalFuns.op210 _ (selected ops) = @ExternalFuns.op210 _ ops := by
  exact PV_B2_E_Install250.preserved_210 ops
theorem preserved_211 (ops : ExternalFuns) : @ExternalFuns.op211 _ (selected ops) = @ExternalFuns.op211 _ ops := by
  exact PV_B2_E_Install250.preserved_211 ops
theorem preserved_212 (ops : ExternalFuns) : @ExternalFuns.op212 _ (selected ops) = @ExternalFuns.op212 _ ops := by
  exact PV_B2_E_Install250.preserved_212 ops
theorem preserved_213 (ops : ExternalFuns) : @ExternalFuns.op213 _ (selected ops) = @ExternalFuns.op213 _ ops := by
  exact PV_B2_E_Install250.preserved_213 ops
theorem preserved_214 (ops : ExternalFuns) : @ExternalFuns.op214 _ (selected ops) = @ExternalFuns.op214 _ ops := by
  exact PV_B2_E_Install250.preserved_214 ops
theorem preserved_215 (ops : ExternalFuns) : @ExternalFuns.op215 _ (selected ops) = @ExternalFuns.op215 _ ops := by
  exact PV_B2_E_Install250.preserved_215 ops
theorem preserved_216 (ops : ExternalFuns) : @ExternalFuns.op216 _ (selected ops) = @ExternalFuns.op216 _ ops := by
  exact PV_B2_E_Install250.preserved_216 ops
theorem preserved_217 (ops : ExternalFuns) : @ExternalFuns.op217 _ (selected ops) = @ExternalFuns.op217 _ ops := by
  exact PV_B2_E_Install250.preserved_217 ops
theorem preserved_218 (ops : ExternalFuns) : @ExternalFuns.op218 _ (selected ops) = @ExternalFuns.op218 _ ops := by
  exact PV_B2_E_Install250.preserved_218 ops
theorem preserved_219 (ops : ExternalFuns) : @ExternalFuns.op219 _ (selected ops) = @ExternalFuns.op219 _ ops := by
  exact PV_B2_E_Install250.preserved_219 ops
theorem preserved_220 (ops : ExternalFuns) : @ExternalFuns.op220 _ (selected ops) = @ExternalFuns.op220 _ ops := by
  exact PV_B2_E_Install250.preserved_220 ops
theorem preserved_221 (ops : ExternalFuns) : @ExternalFuns.op221 _ (selected ops) = @ExternalFuns.op221 _ ops := by
  exact PV_B2_E_Install250.preserved_221 ops
theorem preserved_222 (ops : ExternalFuns) : @ExternalFuns.op222 _ (selected ops) = @ExternalFuns.op222 _ ops := by
  exact PV_B2_E_Install250.preserved_222 ops
theorem preserved_223 (ops : ExternalFuns) : @ExternalFuns.op223 _ (selected ops) = @ExternalFuns.op223 _ ops := by
  exact PV_B2_E_Install250.preserved_223 ops
theorem preserved_224 (ops : ExternalFuns) : @ExternalFuns.op224 _ (selected ops) = @ExternalFuns.op224 _ ops := by
  exact PV_B2_E_Install250.preserved_224 ops
theorem preserved_225 (ops : ExternalFuns) : @ExternalFuns.op225 _ (selected ops) = @ExternalFuns.op225 _ ops := by
  exact PV_B2_E_Install250.preserved_225 ops
theorem preserved_226 (ops : ExternalFuns) : @ExternalFuns.op226 _ (selected ops) = @ExternalFuns.op226 _ ops := by
  exact PV_B2_E_Install250.preserved_226 ops
theorem preserved_227 (ops : ExternalFuns) : @ExternalFuns.op227 _ (selected ops) = @ExternalFuns.op227 _ ops := by
  exact PV_B2_E_Install250.preserved_227 ops
theorem preserved_228 (ops : ExternalFuns) : @ExternalFuns.op228 _ (selected ops) = @ExternalFuns.op228 _ ops := by
  exact PV_B2_E_Install250.preserved_228 ops
theorem preserved_229 (ops : ExternalFuns) : @ExternalFuns.op229 _ (selected ops) = @ExternalFuns.op229 _ ops := by
  exact PV_B2_E_Install250.preserved_229 ops
theorem preserved_230 (ops : ExternalFuns) : @ExternalFuns.op230 _ (selected ops) = @ExternalFuns.op230 _ ops := by
  exact PV_B2_E_Install250.preserved_230 ops
theorem preserved_231 (ops : ExternalFuns) : @ExternalFuns.op231 _ (selected ops) = @ExternalFuns.op231 _ ops := by
  exact PV_B2_E_Install250.preserved_231 ops
theorem preserved_232 (ops : ExternalFuns) : @ExternalFuns.op232 _ (selected ops) = @ExternalFuns.op232 _ ops := by
  exact PV_B2_E_Install250.preserved_232 ops
theorem preserved_233 (ops : ExternalFuns) : @ExternalFuns.op233 _ (selected ops) = @ExternalFuns.op233 _ ops := by
  exact PV_B2_E_Install250.preserved_233 ops
theorem preserved_234 (ops : ExternalFuns) : @ExternalFuns.op234 _ (selected ops) = @ExternalFuns.op234 _ ops := by
  exact PV_B2_E_Install250.preserved_234 ops
theorem preserved_235 (ops : ExternalFuns) : @ExternalFuns.op235 _ (selected ops) = @ExternalFuns.op235 _ ops := by
  exact PV_B2_E_Install250.preserved_235 ops
theorem preserved_236 (ops : ExternalFuns) : @ExternalFuns.op236 _ (selected ops) = @ExternalFuns.op236 _ ops := by
  exact PV_B2_E_Install250.preserved_236 ops
theorem preserved_237 (ops : ExternalFuns) : @ExternalFuns.op237 _ (selected ops) = @ExternalFuns.op237 _ ops := by
  exact PV_B2_E_Install250.preserved_237 ops
theorem preserved_238 (ops : ExternalFuns) : @ExternalFuns.op238 _ (selected ops) = @ExternalFuns.op238 _ ops := by
  exact PV_B2_E_Install250.preserved_238 ops
theorem preserved_239 (ops : ExternalFuns) : @ExternalFuns.op239 _ (selected ops) = @ExternalFuns.op239 _ ops := by
  exact PV_B2_E_Install250.preserved_239 ops
theorem preserved_240 (ops : ExternalFuns) : @ExternalFuns.op240 _ (selected ops) = @ExternalFuns.op240 _ ops := by
  exact PV_B2_E_Install250.preserved_240 ops
theorem preserved_241 (ops : ExternalFuns) : @ExternalFuns.op241 _ (selected ops) = @ExternalFuns.op241 _ ops := by
  exact PV_B2_E_Install250.preserved_241 ops
theorem preserved_242 (ops : ExternalFuns) : @ExternalFuns.op242 _ (selected ops) = @ExternalFuns.op242 _ ops := by
  exact PV_B2_E_Install250.preserved_242 ops
theorem preserved_243 (ops : ExternalFuns) : @ExternalFuns.op243 _ (selected ops) = @ExternalFuns.op243 _ ops := by
  exact PV_B2_E_Install250.preserved_243 ops
theorem preserved_244 (ops : ExternalFuns) : @ExternalFuns.op244 _ (selected ops) = @ExternalFuns.op244 _ ops := by
  exact PV_B2_E_Install250.preserved_244 ops
theorem preserved_245 (ops : ExternalFuns) : @ExternalFuns.op245 _ (selected ops) = @ExternalFuns.op245 _ ops := by
  exact PV_B2_E_Install250.preserved_245 ops
theorem preserved_246 (ops : ExternalFuns) : @ExternalFuns.op246 _ (selected ops) = @ExternalFuns.op246 _ ops := by
  exact PV_B2_E_Install250.preserved_246 ops
theorem preserved_247 (ops : ExternalFuns) : @ExternalFuns.op247 _ (selected ops) = @ExternalFuns.op247 _ ops := by
  exact PV_B2_E_Install250.preserved_247 ops
theorem preserved_248 (ops : ExternalFuns) : @ExternalFuns.op248 _ (selected ops) = @ExternalFuns.op248 _ ops := by
  exact PV_B2_E_Install250.preserved_248 ops
theorem preserved_251 (ops : ExternalFuns) : @ExternalFuns.op251 _ (selected ops) = @ExternalFuns.op251 _ ops := by
  exact PV_B2_E_Install250.preserved_251 ops
theorem preserved_252 (ops : ExternalFuns) : @ExternalFuns.op252 _ (selected ops) = @ExternalFuns.op252 _ ops := by
  exact PV_B2_E_Install250.preserved_252 ops
theorem preserved_253 (ops : ExternalFuns) : @ExternalFuns.op253 _ (selected ops) = @ExternalFuns.op253 _ ops := by
  exact PV_B2_E_Install250.preserved_253 ops
theorem preserved_254 (ops : ExternalFuns) : @ExternalFuns.op254 _ (selected ops) = @ExternalFuns.op254 _ ops := by
  exact PV_B2_E_Install250.preserved_254 ops
theorem preserved_255 (ops : ExternalFuns) : @ExternalFuns.op255 _ (selected ops) = @ExternalFuns.op255 _ ops := by
  exact PV_B2_E_Install250.preserved_255 ops
theorem preserved_256 (ops : ExternalFuns) : @ExternalFuns.op256 _ (selected ops) = @ExternalFuns.op256 _ ops := by
  exact PV_B2_E_Install250.preserved_256 ops
theorem preserved_257 (ops : ExternalFuns) : @ExternalFuns.op257 _ (selected ops) = @ExternalFuns.op257 _ ops := by
  exact PV_B2_E_Install250.preserved_257 ops
theorem preserved_258 (ops : ExternalFuns) : @ExternalFuns.op258 _ (selected ops) = @ExternalFuns.op258 _ ops := by
  exact PV_B2_E_Install250.preserved_258 ops
theorem preserved_259 (ops : ExternalFuns) : @ExternalFuns.op259 _ (selected ops) = @ExternalFuns.op259 _ ops := by
  exact PV_B2_E_Install250.preserved_259 ops
theorem preserved_260 (ops : ExternalFuns) : @ExternalFuns.op260 _ (selected ops) = @ExternalFuns.op260 _ ops := by
  exact PV_B2_E_Install250.preserved_260 ops
theorem preserved_261 (ops : ExternalFuns) : @ExternalFuns.op261 _ (selected ops) = @ExternalFuns.op261 _ ops := by
  exact PV_B2_E_Install250.preserved_261 ops
#print axioms originalOps
#print axioms originalGamma
#print axioms refines
#print axioms total
#print axioms values_injective
#print axioms copy_equal_original
#print axioms callback
#print axioms selected
#print axioms originalDictionary
#print axioms selected_callback
#print axioms gamma_law
#print axioms nonfailure
#print axioms nonvacuity
#print axioms ordinary_preserved
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
#print axioms preserved_251
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
end PV_B2_E_GammaOriginal
