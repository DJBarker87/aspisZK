import NJL_CachedPowers
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJL_CacheReads
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode)
open FIv_PreparedNew (NP)
theorem paired {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
 (relation : List.Forall₂ R xs ys) : ∀ i (hi : i<xs.length) (hj : i<ys.length),R xs[i] ys[i] := by
 induction relation with
 | nil => intro i hi hj;simp at hi
 | cons first tail ih =>
  intro i hi hj
  cases i with
  | zero => exact first
  | succ i => exact ih i (by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using hi) (by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using hj)
def power {lambda : NQ} (p : NJL_CachedPowers.Packet lambda) (i : Fin 8) : NQ :=
 p.powers[i.val]'(by rw [p.eight];exact i.isLt)
def cache {lambda : NQ} (p : NJL_CachedPowers.Packet lambda) (i : Fin 8) : NP :=
 p.caches.val[i.val]'(by rw [p.caches.property,p.eight];exact i.isLt)
theorem canonical {lambda : NQ} (p : NJL_CachedPowers.Packet lambda) (i : Fin 8) : Canon (power p i) :=
 p.canonical _ (List.getElem_mem _)
theorem constructor {lambda : NQ} (p : NJL_CachedPowers.Packet lambda) (i : Fin 8) :
 FIq_Native.field.PreparedQm31Multiplier.new (power p i)=ok (cache p i) ∧ NJB_PreparedLaws.Domain (cache p i) (power p i) :=
 paired p.domains i.val (by rw [p.eight];exact i.isLt) (by rw [p.caches.property,p.eight];exact i.isLt)
theorem value {lambda : NQ} (p : NJL_CachedPowers.Packet lambda) (i : Fin 8) :
 decode (power p i)=decode lambda^(i.val+1) := by
 have v := p.values i.val (by rw [p.eight];exact i.isLt)
 change decode (power p i)=_ at v
 rw [v,pow_succ]
 ring
#print axioms paired
#print axioms canonical
#print axioms constructor
#print axioms value
end AspisR1.NJL_CacheReads
end
