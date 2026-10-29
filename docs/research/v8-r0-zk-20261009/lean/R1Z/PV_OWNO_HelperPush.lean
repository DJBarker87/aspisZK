import R1Z.PV_OWNO_HelperArrays
set_option autoImplicit false
namespace R1Z.PV_OWNO_HelperPush
open PV_OWNK_TowerCanon PV_OWNO_HelperResult PV_OWNO_HelperArrays

/-- Forward source loop: a successful row is pushed before the next row runs.
On a pole the already initialized prefix is not returned as a successful value.
Its destructor/world association is a separate OwnedPublicPlan obligation. -/
def run (inverse : Q → Option Q) (chi : Q) :
 Nat → List CopyRow → List Q → Except Pole (List Q)
 | _,[],acc => .ok acc
 | index,r::rs,acc => match rowResult inverse chi index (view r) with
   | .error e => .error e
   | .ok value => run inverse chi (index+1) rs (acc ++ [value])

theorem successful_canonical (inverse : Q → Option Q) (chi : Q)
 (index : Nat) (rs : List CopyRow) (acc out : List Q)
 (ha : ∀ q ∈ acc, Canon q) (h : run inverse chi index rs acc = .ok out) :
 ∀ q ∈ out, Canon q := by
 induction rs generalizing index acc with
 | nil => exact Except.ok.inj h ▸ ha
 | cons r rs ih =>
  cases hr : rowResult inverse chi index (view r) with
  | error e => simp only [run,hr] at h; cases h
  | ok value =>
   apply ih (index+1) (acc ++ [value])
   · intro q hq
     rcases List.mem_append.mp hq with hq | hq
     · exact ha q hq
     · have he : q = value := by simpa only [List.mem_singleton] using hq
       simpa only [he] using row_canonical inverse chi index r value hr
   · simpa only [run,hr] using h

theorem successful_length (inverse : Q → Option Q) (chi : Q)
 (index : Nat) (rs : List CopyRow) (acc out : List Q)
 (h : run inverse chi index rs acc = .ok out) : out.length = acc.length + rs.length := by
 induction rs generalizing index acc with
 | nil => cases Except.ok.inj h; simp only [List.length_nil,Nat.add_zero]
 | cons r rs ih =>
  cases hr : rowResult inverse chi index (view r) with
  | error e => simp only [run,hr] at h; cases h
  | ok value =>
   have ht : run inverse chi (index+1) rs (acc ++ [value]) = .ok out := by
    simpa only [run,hr] using h
   have hl := ih (index+1) (acc ++ [value]) ht
   simp only [List.length_append,List.length_singleton,List.length_cons,List.length_nil] at hl ⊢
   omega

#print axioms successful_canonical
#print axioms successful_length
end R1Z.PV_OWNO_HelperPush
