import NEU_DecoderProjections
set_option autoImplicit false
noncomputable section
namespace NEX_StatementExt
open Aeneas Aeneas.Std
open AspisR1TerminalDecoder.pool_v1.pair_forest_terminal
abbrev Statement := PoolV1PairForestTerminalStatementV1

def project (s : Statement) (slot : Fin 26) (i : Fin 8) (j : Fin 32) (k : Fin 20) : Nat :=
 match s with
 | .PrivateTransfer c p =>
   if slot.val=0 then 1 else
   if h : slot.val<16 then
     NEU_CommonProjections.value (NED_ReconstructCarriers.toRawCommon c) ⟨slot.val-1,by omega⟩ i j k
   else if h : slot.val<24 then
     NEU_PublicProjections.transfer (NED_PaymentCohorts.toRawTransfer p) ⟨slot.val-16,by omega⟩ i j
   else 0
 | .Withdrawal c p =>
   if slot.val=0 then 2 else
   if h : slot.val<16 then
     NEU_CommonProjections.value (NED_ReconstructCarriers.toRawCommon c) ⟨slot.val-1,by omega⟩ i j k
   else if h : slot.val<23 then
     NEU_PublicProjections.withdrawal (NED_PaymentCohorts.toRawWithdrawal p) ⟨slot.val-16,by omega⟩ i j
   else if slot.val=24 then
     NEU_PublicProjections.withdrawal (NED_PaymentCohorts.toRawWithdrawal p) ⟨7,by decide⟩ i j
   else if slot.val=25 then
     NEU_PublicProjections.withdrawal (NED_PaymentCohorts.toRawWithdrawal p) ⟨8,by decide⟩ i j
   else 0

theorem complete (a b : Statement)
 (point : ∀ slot i j k, project a slot i j k=project b slot i j k) : a=b := by
 cases a with
 | PrivateTransfer c p =>
  cases b with
  | PrivateTransfer d q =>
   apply NEU_DecoderProjections.transfer_ext
   · intro slot i j k
     have h := point ⟨slot.val+1,by omega⟩ i j k
     simpa [project,show slot.val+1≠0 by omega,show slot.val+1<16 by omega] using h
   · intro slot i j
     have h := point ⟨slot.val+16,by omega⟩ i j ⟨0,by decide⟩
     simpa [project,show slot.val+16≠0 by omega,show ¬slot.val+16<16 by omega,show slot.val+16<24 by omega] using h
  | Withdrawal d q =>
   have bad := point ⟨0,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩
   simp [project] at bad
 | Withdrawal c p =>
  cases b with
  | PrivateTransfer d q =>
   have bad := point ⟨0,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩
   simp [project] at bad
  | Withdrawal d q =>
   apply NEU_DecoderProjections.withdrawal_ext
   · intro slot i j k
     have h := point ⟨slot.val+1,by omega⟩ i j k
     simpa [project,show slot.val+1≠0 by omega,show slot.val+1<16 by omega] using h
   · intro slot i j
     by_cases small : slot.val<7
     · have h := point ⟨slot.val+16,by omega⟩ i j ⟨0,by decide⟩
       simpa [project,show slot.val+16≠0 by omega,show ¬slot.val+16<16 by omega,show slot.val+16<23 by omega] using h
     · by_cases seven : slot.val=7
       · have same : slot=⟨7,by decide⟩ := Fin.ext seven
         subst slot
         exact point ⟨24,by decide⟩ i j ⟨0,by decide⟩
       · have eight : slot=⟨8,by decide⟩ := Fin.ext (by change slot.val=8; omega)
         subst slot
         exact point ⟨25,by decide⟩ i j ⟨0,by decide⟩

#print axioms complete
end NEX_StatementExt
