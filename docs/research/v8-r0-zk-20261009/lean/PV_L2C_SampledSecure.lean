import PV_L2C_SamplerFill
import PV_L2C_SecureGuard
import PV_L2C_PaddingNative
set_option autoImplicit false
namespace PV_L2C_SampledSecure
open Aeneas Aeneas.Std Result PV_L2C_NativeQ PV_L2C_StateSampler PV_L2C_PaddingNative

def table (values : List Q) : Fin 1024 → Q := fun r => values[r.val]!

theorem sampled {S : Type} (next : S → Result (PV_L2C_M31.word × S))
    (fuel : Nat) (s s1 : S) (values : List Q)
    (h : PV_L2C_SamplerFill.fill (secure next fuel) 1024 s = ok (.ok values,s1)) :
    ∀ r : Fin 1024, Canonical (table values r) := by
  obtain ⟨hl,hc⟩ := PV_L2C_SamplerFill.secure next 1024 fuel s s1 values h
  intro r
  have hr : r.val < values.length := by rw [hl];exact r.isLt
  apply hc
  rw [table,getElem!_pos values r.val hr]
  exact List.getElem_mem hr
#print axioms sampled

def column (active : Fin 1024 → Bool) (d : Fin 1024) (values : List Q) : Nat → Q :=
  fun r => if h : r < 1024 then rebalance active d (table values) ⟨r,h⟩ else zero

theorem guard {S : Type} (next : S → Result (PV_L2C_M31.word × S))
    (fuel : Nat) (s s1 : S) (values : List Q)
    (h : PV_L2C_SamplerFill.fill (secure next fuel) 1024 s = ok (.ok values,s1))
    (active : Fin 1024 → Bool) (d : Fin 1024) :
    PV_L2C_SecureGuard.loop 1024 0 (column active d values) = ok (.ok ()) := by
  apply PV_L2C_SecureGuard.column
  intro r hr hr'
  unfold column
  rw [dif_pos (by omega)]
  exact rebalance_canonical active d (table values) (sampled next fuel s s1 values h) _
#print axioms guard

theorem audit {S : Type} (next : S → Result (PV_L2C_M31.word × S))
    (fuel : Nat) (s s1 : S) (values : List Q)
    (h : PV_L2C_SamplerFill.fill (secure next fuel) 1024 s = ok (.ok values,s1))
    (active : Fin 1024 → Bool) (d : Fin 1024) (hd : active d = false) :
    PV_L2C_QFold.tableSum (PV_L2C_QFold.inactiveTable active (rebalance active d (table values))) = zero :=
  raw_sum_zero active d (table values) (sampled next fuel s s1 values h) hd
#print axioms audit
end PV_L2C_SampledSecure
