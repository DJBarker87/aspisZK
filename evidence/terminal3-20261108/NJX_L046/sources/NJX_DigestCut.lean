import NJX_DigestPacket
import NJB_PreparedCarrier
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJX_DigestCut
open Aeneas Aeneas.Std
open FIv_NativeArithmetic (NQ)
open FIv_PreparedNew (NP)
open NJX_DigestResiduals (Digest Residuals)
/-- Read-only native observation record. Only the arbitrary seek's asserted
fields enter Cut; all other observed fields remain unrestricted. -/
structure Log where
 kind : Nat → Nat
 left right : Nat → NQ
 packs : Nat → Fin 4 → NQ
 caches : Nat → NJB_PreparedCarrier.Index → NJB_PreparedCarrier.Index → U32
/-- NJX_left_global_cut (K001/K002), all arbitrary seek/limb/pack/cache
coordinates. Direct transcription of calls21, source kinds/arguments,
full9word constructor reply identity, both packs and complete2cell reply.
No child-value or success equation is a premise of this cut. -/
def Cut (high : NQ) (o : Residuals) (d : Digest) (p : NP)
 (lifted residual : Residuals) (packed reply out : Fin 2 → NQ) (l : Log) (calls : Nat) : Prop :=
 calls=21 ∧ l.kind 0=3 ∧ l.left 0=high ∧
 (∀ i : Fin 8,l.kind (1+2*i.val)=5 ∧
  l.left (1+2*i.val)=FIw_ScalarArithmetic.lifted (d i) ∧
  l.kind (2+2*i.val)=2 ∧ l.left (2+2*i.val)=o i ∧ l.right (2+2*i.val)=lifted i) ∧
 (∀ g : Fin 2,l.kind (17+2*g.val)=6 ∧ l.packs (17+2*g.val)=NJX_DigestGroups.group residual g ∧
  l.kind (18+2*g.val)=4 ∧ l.caches (18+2*g.val)=NJB_PreparedCarrier.words p ∧
  l.right (18+2*g.val)=packed g ∧ out g=reply g)

/-- Observation witness built from the actual packet's SAME complete child
Results. It is a conclusion of the root, never an admitted endpoint premise. -/
def log {high : NQ} {o : Residuals} {d : Digest} (p : NJX_DigestPacket.Packet high o d) : Log :=
 {kind := fun n=>if n=0 then 3 else if n<17 then (if n%2=1 then 5 else 2) else if n%2=1 then 6 else 4
  left := fun n=>if n=0 then high else if h:n<17 then
   (if n%2=1 then FIw_ScalarArithmetic.lifted (d ⟨(n-1)/2,by omega⟩) else o ⟨(n-1)/2,by omega⟩) else FIq_Native.field.QM31.ZERO
  right := fun n=>if h:n<17 then FIw_ScalarArithmetic.lifted (d ⟨(n-1)/2,by omega⟩)
   else if h:n<21 then p.packed ⟨(n-18)/2,by omega⟩ else FIq_Native.field.QM31.ZERO
  packs := fun n=>if h:n=17 then NJX_DigestGroups.group p.residual 0 else NJX_DigestGroups.group p.residual 1
  caches := fun _=>NJB_PreparedCarrier.words p.prepared}

theorem source {high : NQ} {o : Residuals} {d : Digest} (p : NJX_DigestPacket.Packet high o d) :
 Cut high o d p.prepared (fun i=>FIw_ScalarArithmetic.lifted (d i)) p.residual p.packed p.out p.out (log p) 21 := by
 refine ⟨rfl,rfl,rfl,?_,?_⟩
 · intro i
   fin_cases i <;> exact ⟨rfl,rfl,rfl,rfl,rfl⟩
 · intro g
   fin_cases g <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
#print source
#print axioms source
end AspisR1.NJX_DigestCut
end
