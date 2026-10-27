import CPP_Metadata
import Hist_Nonvacuity
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPP_BankCache
open Aeneas Aeneas.Std Result S2W_D189Entry Hist_Store

/-- Local cached-account branch of Agave's transaction-boundary loader.
This is not applied between CPIs or asserted to certify a deployed validator. -/
structure Account where
  record : Record
  data : Slice U8

def load (account : Account) : Option Account :=
  if account.record.lamports = 0 then none else some account

def image (account : Account) : Slice U8 :=
  match load account with
  | none => ⟨[],by simp; scalar_tac⟩
  | some value => value.data

theorem loaded (account value : Account) (h : load account = some value) :
    value = account ∧ 0 < value.record.lamports := by
  unfold load at h
  split at h
  · cases h
  · have eq := Option.some.inj h
    subst value
    exact ⟨rfl,by omega⟩

theorem live (account : Account) (h : 0 < account.record.lamports) :
    load account = some account := by
  exact if_neg (by omega)

theorem dead_image (account : Account) (h : account.record.lamports = 0) :
    (image account).val = [] := by
  simp only [image,load,if_pos h]

theorem marker_live (account : Account) (marker : Initialized (image account)) :
    0 < account.record.lamports := by
  by_contra notPositive
  have zero : account.record.lamports = 0 := by omega
  have length := marker.1
  rw [dead_image account zero] at length
  simp only [List.length_nil] at length
  omega

#print axioms loaded
#print axioms live
#print axioms dead_image
#print axioms marker_live
end AspisR1.CPP_BankCache
end
