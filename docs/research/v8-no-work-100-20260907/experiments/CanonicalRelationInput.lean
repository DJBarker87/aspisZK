import CanonicalCollect
import OptimizedRelationRefinement
import AspisFormal.V5ComponentCQM31TowerExact

/-! Field/list projection of the actual V8 fixed-field parser. Length guards,
16-byte offsets, all697 canonical decodes, and the new417/441 relation/final
offsets are constructed here. This is not the old V7 641-field layout, a
mutable-Rust translation, or a complete Wire/authentication refinement. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 30000
namespace AspisV8.CanonicalRelationInput
noncomputable section
open AspisV5ComponentCQM31Representation AspisV5ComponentCQM31TowerExact
open AspisV5ComponentCRejectionSampler AspisV6TranscriptRelationGrammar
open AspisV8.OptimizedRelationRefinement
abbrev K := QM31Exact

def badLength (n : Nat) : Prop :=
  n<24890 ∨ 40282<n ∨ (n-11228-22*621)%52≠0

instance (n : Nat) : Decidable (badLength n) := by unfold badLength; infer_instance

theorem length_shape (n : Nat) :
    ¬badLength n ↔ ∃ frontier : Nat, frontier≤296 ∧ n=24890+52*frontier := by
  constructor
  · intro good
    unfold badLength at good
    refine ⟨(n-24890)/52,?_,?_⟩ <;> omega
  · rintro ⟨frontier,cap,rfl⟩
    unfold badLength
    omega

/-- Source fixed-byte slice: each of697 fields has exactly16 bytes. getD is
only a totalized definition; success_in_bounds removes its fallback. -/
def fieldBytes (body : List Byte) (field : Fin 697) : QM31Bytes :=
  fun byte=>body.getD (16*field.val+byte.val) 0

def parseFixed (body : List Byte) : Option (List K) :=
  if badLength body.length then none else
    CanonicalCollect.collect decodeQM31ExactLE (List.ofFn (fieldBytes body))

theorem malformed_length (body : List Byte) (bad : badLength body.length) :
    parseFixed body=none := by
  simp only [parseFixed,if_pos bad]

theorem parse_success (body : List Byte) (values : List K)
    (success : parseFixed body=some values) :
    ¬badLength body.length ∧ values.length=697 ∧
      ∀ field : Fin 697, decodeQM31ExactLE (fieldBytes body field)=
        some (values.getD field.val 0) := by
  unfold parseFixed at success
  split at success
  · contradiction
  · rename_i good
    exact ⟨good,CanonicalCollect.success_ofFn decodeQM31ExactLE
      (fieldBytes body) values 0 success⟩

theorem success_in_bounds (body : List Byte) (values : List K)
    (success : parseFixed body=some values) (field : Fin 697) (byte : Fin 16) :
    16*field.val+byte.val<body.length := by
  have good := (parse_success body values success).1
  have hi := field.isLt
  have hb := byte.isLt
  unfold badLength at good
  omega

theorem fieldBytes_exact (body : List Byte) (values : List K)
    (success : parseFixed body=some values) (field : Fin 697) (byte : Fin 16) :
    fieldBytes body field byte=
      body[16*field.val+byte.val]'(success_in_bounds body values success field byte) := by
  exact List.getD_eq_getElem _ _ (success_in_bounds body values success field byte)

theorem noncanonical_field (bytes : QM31Bytes) (limb : Fin 4)
    (high : m31Modulus≤(decodeWordLE (qm31LimbBytes bytes limb)).val) :
    decodeQM31ExactLE bytes=none := by
  have bad : ¬∀ j, (decodeWordLE (qm31LimbBytes bytes j)).val < m31Modulus := by
    intro all
    exact (not_lt_of_ge high) (all limb)
  simp only [decodeQM31ExactLE,decodeQM31LE,dif_neg bad,Option.map_none]

/-- Any bad limb in any fixed field rejects the complete fixed-section
projection, including fields outside the relation response being inspected. -/
theorem noncanonical_reject (body : List Byte) (field : Fin 697) (limb : Fin 4)
    (high : m31Modulus≤(decodeWordLE (qm31LimbBytes (fieldBytes body field) limb)).val) :
    parseFixed body=none := by
  cases result : parseFixed body with
  | none => rfl
  | some values =>
    have decoded := (parse_success body values result).2.2 field
    rw [noncanonical_field _ limb high] at decoded
    contradiction

def relationIndex (round : Fin 4) (sent : Fin 6) : Fin 697 :=
  ⟨417+6*round.val+sent.val,by omega⟩
def finalIndex (coefficient : Fin 256) : Fin 697 :=
  ⟨441+coefficient.val,by omega⟩

def parts (f : Fin 6 → K) : Sent K :=
  ⟨f 0,f 1,f 2,f 3,f 4,f 5⟩

theorem parts_sent (f : Fin 6 → K) (j : Fin 6) :
    (parts f).sent j=f j := by
  fin_cases j <;> rfl

def response (values : List K) (round : Fin 4) : Sent K :=
  parts (fun j=>values.getD (relationIndex round j).val 0)

theorem response_sent (values : List K) (round : Fin 4) (sent : Fin 6) :
    (response values round).sent sent=values.getD (417+6*round.val+sent.val) 0 :=
  parts_sent _ _

theorem decoded_response (body : List Byte) (values : List K)
    (success : parseFixed body=some values) (round : Fin 4) (sent : Fin 6) :
    decodeQM31ExactLE (fieldBytes body (relationIndex round sent))=
      some ((response values round).sent sent) := by
  rw [response_sent]
  exact (parse_success body values success).2.2 (relationIndex round sent)

theorem decoded_final (body : List Byte) (values : List K)
    (success : parseFixed body=some values) (coefficient : Fin 256) :
    decodeQM31ExactLE (fieldBytes body (finalIndex coefficient))=
      some (values.getD (441+coefficient.val) 0) :=
  (parse_success body values success).2.2 (finalIndex coefficient)

/-- All six sent coefficients occupy exactly0,1,2,3,5,6 of the actual
compact polynomial; the missing quartic is reconstructed from the claim. -/
theorem compact_keeps_six (values : List K) (round : Fin 4)
    (quarter claim : K) (sent : Fin 6) :
    relationCoefficient quarter claim (response values round) (![0,1,2,3,5,6] sent)=
      values.getD (417+6*round.val+sent.val) 0 := by
  rw [compact_sent_not_omitted,response_sent]

theorem compact_quartic (values : List K) (round : Fin 4) (quarter claim : K) :
    relationCoefficient quarter claim (response values round) 4=
      claim*quarter-values.getD (417+6*round.val) 0 := rfl

theorem decoded_boundary (values : List K) (round : Fin 4) (quarter claim : K)
    (hq : quarter*4=1) :
    JointImageGame.boundary (claimed quarter claim (response values round))=claim :=
  claimed_boundary quarter claim (response values round) hq

#print axioms length_shape
#print axioms parse_success
#print axioms success_in_bounds
#print axioms fieldBytes_exact
#print axioms noncanonical_field
#print axioms noncanonical_reject
#print axioms decoded_response
#print axioms decoded_final
#print axioms compact_keeps_six
#print axioms compact_quartic
#print axioms decoded_boundary
end
end AspisV8.CanonicalRelationInput
