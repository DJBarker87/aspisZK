import R1Z.PV_OWNJ_Points
import R1Z.PV_OWNI_PublicPlan
set_option autoImplicit false
namespace R1Z.PV_OWNJ_Claims
open PV_OWNI_RawOps PV_OWNJ_Points

def evaluate (point column : List Q) : Option Q :=
 PV_OWNI_RawConsumer.value point column (PV_OWNI_Scanner.width point)
  (PV_OWNI_Scanner.trailing point) (PV_OWNI_Scanner.suffix point)

def lanes (point : List Q) : List (List Q) → Option (List Q)
 | [] => some []
 | c::cs => do
   let q ← evaluate point c
   let rest ← lanes point cs
   some (q::rest)

def points (columns : List (List Q)) : List (List Q) → Option (List (List Q))
 | [] => some []
 | p::ps => do
   let claim ← lanes p columns
   let rest ← points columns ps
   some (claim::rest)

def point_claims (columns : List (List Q)) (point : List Q) : Option (List (List Q)) :=
 points columns (statement_points point)

theorem evaluate_wrong (p c : List Q) (h : c.length ≠ 1024) : evaluate p c = none := by
 unfold evaluate PV_OWNI_RawConsumer.value
 exact if_pos h

theorem lanes_first_wrong (p : List Q) (before after : List (List Q)) (bad : List Q)
 (h : bad.length ≠ 1024) : lanes p (before ++ bad::after) = none := by
 induction before with
 | nil => simp only [List.nil_append,lanes,evaluate_wrong p bad h,Option.bind_none]
   rfl
 | cons c cs ih =>
  simp only [List.cons_append,lanes,ih]
  cases evaluate p c <;> rfl

theorem point_claims_wrong (point : List Q) (before after : List (List Q)) (bad : List Q)
 (h : bad.length ≠ 1024) : point_claims (before ++ bad::after) point = none := by
 simp only [point_claims,statement_points,points,lanes_first_wrong point before after bad h,
  Option.bind_none]
 rfl

/-- Columns are built by 26 length-preserving lifts followed by three
fixed-array copies; the helper has passed its 1024-element conversion. -/
def built_columns (base : List (List Q)) (h1 g d : List Q) : List (List Q) :=
 base ++ [h1,g,d]

theorem built_lengths (base : List (List Q)) (h1 g d : List Q)
 (hb : base.length = 26) (hc : ∀ c ∈ base, c.length = 1024)
 (hh : h1.length = 1024) (hg : g.length = 1024) (hd : d.length = 1024) :
 (built_columns base h1 g d).map List.length = List.replicate 29 1024 := by
 have he0 : base.map List.length = List.replicate (base.map List.length).length 1024 := by
  apply List.eq_replicate_of_mem
  intro n hn
  obtain ⟨c,hc',rfl⟩ := List.mem_map.mp hn
  exact hc c hc'
 have he : base.map List.length = List.replicate base.length 1024 := by
  simpa only [List.length_map] using he0
 simp only [built_columns,List.map_append,List.map_cons,List.map_nil,he,hb,hh,hg,hd]
 rfl

#print axioms evaluate_wrong
#print axioms lanes_first_wrong
#print axioms point_claims_wrong
#print axioms built_lengths
end R1Z.PV_OWNJ_Claims
