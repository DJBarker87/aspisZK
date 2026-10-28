import PV_L2C_N3Guard
import PV_L2C_SampledBase
import PV_L2C_SampledMaskOnly
import PV_L2C_SampledSecure
set_option autoImplicit false
noncomputable section
namespace PV_L2C_MaterialN3
open Aeneas Aeneas.Std Result PV_L2C_M31 PV_L2C_StateSampler

/-- Source-call executions at the value cut, retaining start/end states and
sample failures. This stores no canonical-column or guard-success premise.
Native state/ownership/control association remains a separately audited cut. -/
structure Executions (S D : Type) (next : S → Result (word × S))
    (sourceNext : D → Result (word × D)) (input : PV_L2C_MaskRange.Bank) where
  active : Fin 1024 → Bool
  c1Dependent : Fin 16 → Usize
  cells : List PV_L2C_MaskRange.Cell
  c1Start : S
  c1End : S
  c1 : PV_L2C_MaskRange.Bank
  c1Returned : PV_L2C_SampledBase.applySampled next 16 input cells active c1Dependent c1Start = ok (.ok c1,c1End)
  maskValues : Fin 10 → List word
  maskStart : Fin 10 → S
  maskEnd : Fin 10 → S
  maskReturned : ∀ c, PV_L2C_SamplerFill.fill (scalar next 16) 1024 (maskStart c) = ok (.ok (maskValues c),maskEnd c)
  maskDependent : Usize
  dValues : List PV_L2C_NativeQ.Q
  dStart : D
  dEnd : D
  dReturned : PV_L2C_SamplerFill.fill (secure sourceNext 16) 1024 dStart = ok (.ok dValues,dEnd)
  gValues : List PV_L2C_NativeQ.Q
  gStart : S
  gEnd : S
  gReturned : PV_L2C_SamplerFill.fill (secure next 16) 1024 gStart = ok (.ok gValues,gEnd)
  qDependent : Fin 1024

def base {S D : Type} {next : S → Result (word × S)} {sourceNext : D → Result (word × D)}
    {input : PV_L2C_MaskRange.Bank} (e : Executions S D next sourceNext input) (c : Fin 26) : List U32 :=
  if h : c.val < 16 then PV_L2C_RouteBaseGuard.column e.c1 ⟨c.val,h⟩
  else List.ofFn (fun r : Fin 1024 => (⟨PV_L2C_SampledMaskOnly.balanced
    (e.maskValues ⟨c.val-16,by have := c.isLt;omega⟩) e.active e.maskDependent r⟩ : U32))

theorem expected {S D : Type} {next : S → Result (word × S)} {sourceNext : D → Result (word × D)}
    {input : PV_L2C_MaskRange.Bank} (e : Executions S D next sourceNext input)
    (hi : PV_L2C_MaskRange.Canonical input) :
    PV_L2C_N3Guard.run (base e)
      (PV_L2C_SampledSecure.column e.active e.qDependent e.dValues)
      (PV_L2C_SampledSecure.column e.active e.qDependent e.gValues) = ok (.ok ()) := by
  apply PV_L2C_N3Guard.expected
  · intro c
    unfold base
    split
    · exact PV_L2C_SampledBase.returned next 16 input hi e.cells e.active e.c1Dependent
        e.c1Start e.c1End e.c1 e.c1Returned _
    · exact PV_L2C_SampledMaskOnly.guard next 16 _ _ _ (e.maskReturned _) e.active e.maskDependent
  · exact PV_L2C_SampledSecure.guard sourceNext 16 e.dStart e.dEnd e.dValues e.dReturned e.active e.qDependent
  · exact PV_L2C_SampledSecure.guard next 16 e.gStart e.gEnd e.gValues e.gReturned e.active e.qDependent
#print axioms expected

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]
include K in
theorem transfer {S D : Type} (next : S → Result (word × S)) (sourceNext : D → Result (word × D))
    (t : PV_L2C_ClientRoute.Transfer)
    (e : Executions S D next sourceNext (PV_L2C_RouteBaseGuard.bank t.compiled.semantic_c1.c1)) :
    PV_L2C_N3Guard.run (base e)
      (PV_L2C_SampledSecure.column e.active e.qDependent e.dValues)
      (PV_L2C_SampledSecure.column e.active e.qDependent e.gValues) = ok (.ok ()) :=
  expected e (PV_L2C_RouteBaseGuard.transfer_bank (K:=K) t)
#print axioms transfer

include K in
theorem withdrawal {S D : Type} (next : S → Result (word × S)) (sourceNext : D → Result (word × D))
    (t : PV_L2C_ClientRoute.Withdrawal)
    (e : Executions S D next sourceNext (PV_L2C_RouteBaseGuard.bank t.compiled.semantic_c1.c1)) :
    PV_L2C_N3Guard.run (base e)
      (PV_L2C_SampledSecure.column e.active e.qDependent e.dValues)
      (PV_L2C_SampledSecure.column e.active e.qDependent e.gValues) = ok (.ok ()) :=
  expected e (PV_L2C_RouteBaseGuard.withdrawal_bank (K:=K) t)
#print axioms withdrawal
end PV_L2C_MaterialN3
