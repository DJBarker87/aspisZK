import NJL_TagReduction
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJL_TagChunk
open Aeneas Aeneas.Std Result
open AspisV8R17.RawReducer (P)
open NJL_TagRawTrace (Selectors dot)
open NJL_TagReduction (State)
def zero : NJL_TagRawStep.State := fun _=>0#u64
def reference (s : Selectors) (terms : List (Fin 272)) (before : State) : Result State := do
 let raw ← NJL_TagRawTrace.run s terms zero
 NJL_TagReduction.run raw [0,1,2,3] before
def Invocation (s : Selectors) (terms : List (Fin 272)) (before after : State) : Prop :=
 ∃ raw,NJL_TagRawTrace.Trace s terms 0 zero raw ∧ NJL_TagReduction.Trace raw [0,1,2,3] before after
/-- One arbitrary source chunk including a partial final chunk. All four
raw cells start at ZERO, and every reduction consumes the actual raw result. -/
theorem source (s : Selectors) (terms : List (Fin 272)) (before : State)
 (small : terms.length≤4) (hs : FIw_ArrayValue.canonical s.high) (hb : ∀ i,(before i).val<P) :
 ∃ after,reference s terms before=ok after ∧ Invocation s terms before after ∧
 (∀ i,(after i).val<P) ∧ (∀ i,(after i).val=((before i).val+dot s terms i)%P) := by
 have hz : ∀ i,(zero i).val=0 := fun _=>rfl
 obtain ⟨raw,cr,tr,vr,_⟩ := NJL_TagRawTrace.source s terms zero 0 (by omega) hs (by intro i;rw [hz];omega)
 obtain ⟨after,ca,ta,ha,va⟩ := NJL_TagReduction.source raw before hb
 refine ⟨after,?_,⟨raw,tr,ta⟩,ha,?_⟩
 · simp only [reference,cr,bind_tc_ok,ca]
 · intro i
   have rawValue : (raw i).val=dot s terms i := by simpa only [hz,Nat.zero_add] using vr i
   rw [va i,rawValue]
   simp only [Nat.add_mod,Nat.mod_mod]
#print source
#print axioms source
end AspisR1.NJL_TagChunk
end
