import DrvC_OraclePort
set_option autoImplicit false
noncomputable section
namespace AspisR1.DrvC_FirstPure
open Aeneas Aeneas.Std Result
open DrvC_Installation DrvC_Carriers Tx1Q_Carriers

theorem result_transport {A B : Type} (f : A → B) (g : B → A)
    (inv : ∀ a, g (f a) = a)
    (m : Result (core.result.Result A AspisR1Stage2.verifier.Error)) :
    DrvC_Program.mapResult (DrvC_Dictionary.reply g) (Tx1Q_Install.result f m) =
      Port3_QueryInstall.result m := by
  cases m with
  | fail e => rfl
  | div => rfl
  | ok r =>
    cases r with
    | Ok a => simp only [Tx1Q_Install.result,bind_tc_ok,DrvC_Program.mapResult,
        DrvC_Dictionary.reply,inv,Port3_QueryInstall.result]
    | Err e => cases e <;> rfl

theorem initial {F C : Type} (c : Configuration F C) :
    DrvC_Program.mapResult (DrvC_Dictionary.reply accumulator)
      ((currentInstalled c).op20 .S2) = Port3_Initial.constructor c.reserved .S2 := by
  change DrvC_Program.mapResult (DrvC_Dictionary.reply accumulator)
    (Tx1Q_PrefixInstall.initial c.reserved .S2) = _
  dsimp only [Tx1Q_PrefixInstall.initial,Tx1Q_Carriers.variant]
  generalize hx : Port3_Initial.constructor c.reserved .S2 = r
  cases r with
  | fail e => rfl
  | div => rfl
  | ok r =>
    cases r with
    | Ok a => simp only [Tx1Q_PrefixInstall.initial,Tx1Q_PrefixInstall.topResult,hx,bind_tc_ok,
        DrvC_Program.mapResult,DrvC_Dictionary.reply,accumulator_roundtrip]
    | Err e => cases e <;> rfl

attribute [local irreducible] Op3I_Source.verifier.candidate.parse_shape

theorem shape {F C : Type} (c : Configuration F C) (proof : Slice U8) :
    DrvC_Program.mapResult (DrvC_Dictionary.reply variant) ((currentInstalled c).op3 proof) =
      (stage c).op3 proof := by
  change DrvC_Program.mapResult (DrvC_Dictionary.reply variant) (Op3I_Install.sourceBody proof) =
    Tx2I_Install.shape proof
  dsimp only [Op3I_Install.sourceBody,Tx2I_Install.shape]
  cases r : Op3I_Source.verifier.candidate.parse_shape Op3I_Std.ops proof with
  | fail e => rfl
  | div => rfl
  | ok r => cases r with
    | Ok v => cases v <;> rfl
    | Err e => cases e <;> rfl

theorem flush {F C : Type} (c : Configuration F C) (b : Tx1Q_Carriers.C.B) (old : Slice Tx1Q_Carriers.C.K) :
    DrvC_Program.mapResult (slice k) ((currentInstalled c).op17 b old) =
      (stage c).op9 (pending b) (slice k old) := by
  change DrvC_Program.mapResult (slice k) (Tx1Q_Install.flush b old) =
    Port3_FlushInstall.flush (pending b) (slice k old)
  unfold Tx1Q_Install.flush
  cases r : Port3_FlushInstall.flush (pending b) (slice k old) with
  | fail e => rfl
  | div => rfl
  | ok out => simp only [bind_tc_ok,DrvC_Program.mapResult,
      DrvC_CurrentSlots.slice_roundtrip unK k k_unK]

#print axioms result_transport
#print axioms initial
#print axioms shape
#print axioms flush
end AspisR1.DrvC_FirstPure
end
