import DrvC_FirstPure
set_option autoImplicit false
noncomputable section
namespace AspisR1.DrvC_QueryTransport
open Aeneas Aeneas.Std Result
open DrvC_Installation DrvC_Carriers Tx1Q_Carriers


theorem query {F C : Type} (c : Configuration F C) (proof : Slice U8)
    (p : Tx1Q_Carriers.C.P) (a : Tx1Q_Carriers.C.A) (g : Array Tx1Q_Carriers.C.E 29#usize)
    (geo : Tx1Q_Carriers.C.G) (b : Tx1Q_Carriers.C.B) (stop : Usize) :
    DrvC_Program.mapResult (DrvC_Dictionary.reply (fun out => (accumulator out.1,pending out.2)))
      ((currentInstalled c).op7 proof p a g none geo b stop) =
    (stage c).op6 proof (prepared p) (accumulator a) (arr e g) none (geometry geo) (pending b) stop := by
  apply DrvC_FirstPure.result_transport
    (fun out : S.A × S.B => (unAccumulator out.1,unPending out.2))
    (fun out => (accumulator out.1,pending out.2))
  intro out
  simp only [accumulator_roundtrip,pending_roundtrip]

theorem top_transport {A B : Type} (f : A → B) (g : B → A) (inv : ∀ a, g (f a) = a)
    (m : Result (core.result.Result A VTop_Stages.verifier.Error)) :
    DrvC_Program.mapResult (DrvC_Dictionary.reply g) (Tx1Q_PrefixInstall.topResult f m) = m := by
  cases m with
  | fail e => rfl
  | div => rfl
  | ok r => cases r with
    | Ok a => simp only [Tx1Q_PrefixInstall.topResult,bind_tc_ok,DrvC_Program.mapResult,
        DrvC_Dictionary.reply,inv]
    | Err e => cases e <;> rfl

theorem pending_call {F C : Type} (c : Configuration F C) (weights : Slice Tx1Q_Carriers.C.K) :
    DrvC_Program.mapResult (DrvC_Dictionary.reply pending)
      ((currentInstalled c).op18 weights) = (stage c).op10 (slice k weights) :=
  top_transport unPending pending pending_roundtrip _

theorem geometry_call {F C : Type} (c : Configuration F C) (qs : Array U32 22#usize) (start stop : Usize) :
    DrvC_Program.mapResult (DrvC_Dictionary.reply geometry)
      ((currentInstalled c).op19 qs start stop) = (stage c).op11 qs start stop :=
  top_transport Tx1Q_PrefixInstall.unGeometry geometry (fun g => by cases g; rfl) _

#print axioms query
#print axioms top_transport
#print axioms pending_call
#print axioms geometry_call
end AspisR1.DrvC_QueryTransport
end
