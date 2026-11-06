import NLU_HighCut
import NLI_FromFnInduction
set_option autoImplicit false
namespace AspisR1.NLU_High
open Aeneas Aeneas.Std AspisR1PublicPreparation
abbrev Memory := NLI_FromFn.Memory
def values (claims : Claims) (i : Nat) : NLU.Q := high claims ⟨i%10,Nat.mod_lt i (by decide)⟩
/-- Only ONE native iteration is interpreted per step. No destination tail is
read. The caller's fixed bound is proved below, not assumed at a136 root. -/
def loop (native : Native) : Nat → Nat → Claims → Memory → Claims×Memory
 | 0,_,claims,memory=>(claims,memory)
 | n+1,start,claims,memory=>
   if inside : start<10 then
    let head:=native claims ⟨start,inside⟩
    loop native n (start+1) head.claims (NLI_FromFn.write memory start head.value)
   else (claims,memory)
theorem induction (native : Native) (cut : Cut native) (count start : Nat)
 (bound : start+count≤10) (claims : Claims) (memory : Memory) :
 loop native count start claims memory=
 (claims,NLI_FromFn.fill (values claims) count start memory) := by
 induction count generalizing start claims memory with
 | zero=>rfl
 | succ n ih=>
   have inside : start<10 := by omega
   have tail : start+1+n≤10 := by omega
   simp only [loop,if_pos inside,complete native cut claims ⟨start,inside⟩]
   rw [ih (start+1) tail]
   simp only [NLI_FromFn.fill]
   have same : values claims start=high claims ⟨start,inside⟩ := by
    unfold values
    simp only [Nat.mod_eq_of_lt inside]
   rw [same]
/-- Initialization and the whole source Claims frame come from the generic
induction and the paired arbitrary-prestate native iteration laws. Parent
stack/heap realization remains outside this conditional inner-loop packet. -/
theorem initialized (native : Native) (cut : Cut native) (claims : Claims) (memory : Memory) :
 (loop native 10 0 claims memory).1=claims ∧
 NLI_FromFn.Initialized (values claims) 10 (loop native 10 0 claims memory).2 := by
 rw [induction native cut 10 0 (by decide)]
 refine ⟨rfl,?_⟩
 exact NLI_FromFn.fill_prefix (values claims) 10 0 memory (by intro i impossible;omega)
#print axioms induction
#print axioms initialized
end AspisR1.NLU_High
