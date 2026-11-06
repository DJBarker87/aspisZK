import NJB_TagReduce
import NJL_TagRawTrace
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJL_TagReduction
open Aeneas Aeneas.Std Result
open AspisV8R17.RawReducer (P)
abbrev State := Fin 4 → U32
def put (s : State) (i : Fin 4) (x : U32) : State := fun j=>if j=i then x else s j
/-- Exact NJB_K070/K071 cut. All counters, operands and all four post cells
are tied to the same input array and same raw array. -/
def Cut (before after : State) (raw : NJL_TagRawStep.State) (limb : Fin 4)
 (residue reply seenLeft seenRight : U32) (seenRaw : U64) (reductions adds next : Nat) : Prop :=
 reductions=1 ∧ adds=1 ∧ seenRaw=raw limb ∧ seenLeft=before limb ∧ seenRight=residue ∧
 next=limb.val+1 ∧ after=put before limb reply
def Step (raw : NJL_TagRawStep.State) (limb : Fin 4) (before after : State) : Prop :=
 ∃ residue reply,FIq_Native.field.M31.reduce_u64 (raw limb)=ok residue ∧
 FIq_Native.field.M31.add (before limb) residue=ok reply ∧
 Cut before after raw limb residue reply (before limb) residue (raw limb) 1 1 (limb.val+1)
def step (raw : NJL_TagRawStep.State) (limb : Fin 4) (before : State) : Result State := do
 let reply ← NJB_TagReduce.reference (before limb) (raw limb)
 ok (put before limb reply)
theorem step_source (raw : NJL_TagRawStep.State) (limb : Fin 4) (before : State)
 (hb : ∀ i,(before i).val<P) :
 ∃ after,step raw limb before=ok after ∧ Step raw limb before after ∧
 (∀ i,(after i).val<P) ∧
 (∀ i,(after i).val=if i=limb then ((before i).val+(raw i).val%P)%P else (before i).val) := by
 obtain ⟨residue,cr,vr,hr⟩ := NJB_TagReduce.reduce (raw limb)
 obtain ⟨reply,ca,va,ha⟩ := NJB_TagReduce.add (before limb) residue (hb limb) hr
 let after := put before limb reply
 refine ⟨after,?_,⟨residue,reply,cr,ca,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,?_,?_⟩
 · simp only [step,NJB_TagReduce.reference,cr,ca,bind_tc_ok];rfl
 · intro i;dsimp only [after,put];split <;> first | exact ha | exact hb i
 · intro i
   by_cases h:i=limb
   · subst i;simp [after,put,va,vr]
   · simp [after,put,h]
inductive Trace (raw : NJL_TagRawStep.State) : List (Fin 4) → State → State → Prop
 | nil (s : State) : Trace raw [] s s
 | cons {i is before middle after} (first : Step raw i before middle)
   (rest : Trace raw is middle after) : Trace raw (i::is) before after
def run (raw : NJL_TagRawStep.State) : List (Fin 4) → State → Result State
 | [],s=>ok s
 | i::is,s=>do
  let middle ← step raw i s
  run raw is middle
/-- Four actual reductions and adds, with the native full-array frame at
EACH limb. The arbitrary raw state is never assumed canonical. -/
theorem source (raw : NJL_TagRawStep.State) (before : State) (hb : ∀ i,(before i).val<P) :
 ∃ after,run raw [0,1,2,3] before=ok after ∧ Trace raw [0,1,2,3] before after ∧
 (∀ i,(after i).val<P) ∧ (∀ i,(after i).val=((before i).val+(raw i).val%P)%P) := by
 obtain ⟨s0,c0,t0,h0,v0⟩ := step_source raw 0 before hb
 obtain ⟨s1,c1,t1,h1,v1⟩ := step_source raw 1 s0 h0
 obtain ⟨s2,c2,t2,h2,v2⟩ := step_source raw 2 s1 h1
 obtain ⟨s3,c3,t3,h3,v3⟩ := step_source raw 3 s2 h2
 refine ⟨s3,?_,.cons t0 (.cons t1 (.cons t2 (.cons t3 (.nil s3)))),h3,?_⟩
 · simp only [run,c0,c1,c2,c3,bind_tc_ok]
 · intro i
   fin_cases i <;> norm_num [v3,v2,v1,v0]
#print step_source
#print axioms step_source
#print source
#print axioms source
end AspisR1.NJL_TagReduction
end
