import NNG_Obs345
-- Canonical rev4 retarget of the retained NMT_R2 std/clone observations.
set_option autoImplicit false
namespace AspisR1.NNG_Pure345
open RSL NNG_Obs345

def silent {A : Type} (x : A) : Obs A := ⟨.ret x,[]⟩
def stopped {A : Type} : Obs A := ⟨.abort,[]⟩
def cloned {A : Type} (keep : Bool) (x : Except ProgramError A) : Obs (Except ProgramError A) :=
 match x with
 | .ok a => silent (.ok a)
 | .error e => if e.cloneAllocates && !keep then stopped else silent (.error e)

theorem cloned_valid {A : Type} (keep : Bool) (x : Except ProgramError A) (env : Env) :
 RS.ofCloned x env (cloned keep x) := by
 cases x with
 | ok a => rfl
 | error e =>
  unfold cloned RS.ofCloned
  cases h : e.cloneAllocates <;> cases keep <;>
   simp only [h,Bool.false_and,Bool.true_and,Bool.not_true,Bool.not_false,
    Bool.false_eq_true,if_false,if_true]
  · rfl
  · rfl
  · exact (RS.alloc_seq_iff _ env _).mpr (Or.inr rfl)
  · exact (RS.alloc_seq_iff _ env _).mpr (Or.inl rfl)

def allocation (keep : Bool) : Obs (Except ProgramError Unit) :=
 if keep then silent (.ok ()) else stopped

theorem allocation_valid (keep : Bool) (env : Env) :
 RS.lift Spec.alloc env (allocation keep) := by
 apply (RS.lift_alloc_iff env _).mpr
 cases keep with
 | false => exact Or.inr rfl
 | true => exact Or.inl rfl

def allocationIf (reached keep : Bool) : Obs (Except ProgramError Unit) :=
 if reached then allocation keep else silent (.ok ())

theorem allocationIf_valid (reached keep : Bool) (env : Env) :
 RS.lift (Spec.allocIf reached) env (allocationIf reached keep) := by
 cases reached with
 | false => exact Or.inl ⟨(),[],⟨.ret (.ok ()),[]⟩,rfl,rfl,rfl⟩
 | true => exact allocation_valid keep env

def check (bad : Bool) (e : ProgramError) : Obs (Except ProgramError Unit) :=
 silent (if bad then .error e else .ok ())

theorem check_valid (bad : Bool) (e : ProgramError) (env : Env) :
 RS.check bad e env (check bad e) := by cases bad <;> rfl

/-- Branch-sensitive refinement of one actual `?` occurrence. Returning Err,
abort and divergence retain their prefix without a continuation premise. -/
theorem try_reachable {A B : Type} (m : RS A) (k : A → RS B)
 (actual : Obs (Except ProgramError A)) (next : A → Obs (Except ProgramError B))
 (env : Env) (first : m env actual)
 (later : ∀ a es, actual = ⟨.ret (.ok a),es⟩ → k a env (next a)) :
 RS.bind m k env (tryObs actual next) := by
 cases actual with
 | mk exit events =>
  cases exit with
  | abort => exact Or.inr (Or.inl ⟨events,first,rfl⟩)
  | diverge => exact Or.inr (Or.inr ⟨events,first,rfl⟩)
  | ret r =>
   cases r with
   | error e => exact Or.inl ⟨.error e,events,⟨.ret (.error e),[]⟩,first,rfl,rfl⟩
   | ok a => exact Or.inl ⟨.ok a,events,next a,first,later a events rfl,rfl⟩
#print axioms cloned_valid
#print axioms allocation_valid
#print axioms allocationIf_valid
#print axioms check_valid
#print axioms try_reachable
end AspisR1.NNG_Pure345
