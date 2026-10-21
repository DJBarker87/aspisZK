import S4N8OutputForwardRootV1
import S4N8WideFromLimbsABI
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FastDotsN8PackForwardRootV1
open AspisR1FastDotsN8WideFromLimbsABI (finishFromLimbsCurrent finishToCurrent)
abbrev U32 := Std.U32
abbrev Ops := AspisR1FastDotsCurrent.FourDotsOps
abbrev Wide := AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact
private theorem xs_length (xs : Array U32 8#usize) : xs.val.length=8 := by
  simpa using xs.property

def word0 (xs : Array U32 8#usize) : U32 :=
  xs.val[0]'(by have hx := xs_length xs; omega)
def word1 (xs : Array U32 8#usize) : U32 :=
  xs.val[1]'(by have hx := xs_length xs; omega)
def word2 (xs : Array U32 8#usize) : U32 :=
  xs.val[2]'(by have hx := xs_length xs; omega)
def word3 (xs : Array U32 8#usize) : U32 :=
  xs.val[3]'(by have hx := xs_length xs; omega)
def word4 (xs : Array U32 8#usize) : U32 :=
  xs.val[4]'(by have hx := xs_length xs; omega)
def word5 (xs : Array U32 8#usize) : U32 :=
  xs.val[5]'(by have hx := xs_length xs; omega)
def word6 (xs : Array U32 8#usize) : U32 :=
  xs.val[6]'(by have hx := xs_length xs; omega)
def word7 (xs : Array U32 8#usize) : U32 :=
  xs.val[7]'(by have hx := xs_length xs; omega)

theorem array_eq_ordered_make (xs : Array U32 8#usize) :
    xs = Array.make 8#usize
      [word0 xs, word1 xs, word2 xs, word3 xs,
       word4 xs, word5 xs, word6 xs, word7 xs] := by
  have hvals : xs.val = (Array.make 8#usize
      [word0 xs, word1 xs, word2 xs, word3 xs,
       word4 xs, word5 xs, word6 xs, word7 xs]).val := by
    apply List.ext_getElem
    · simp [xs_length xs, Array.make]
    · intro i hi₁ hi₂
      have hi : i < 8 := by
        change i < xs.val.length at hi₁
        have hlen := xs_length xs
        omega
      have hiCases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨
          i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
      rcases hiCases with h | h | h | h | h | h | h | h <;> subst i <;>
        simp [word0, word1, word2, word3, word4, word5, word6, word7, Array.make]
  change (xs : {l : List U32 // l.length = (8#usize).val}) =
    (Array.make 8#usize
      [word0 xs, word1 xs, word2 xs, word3 xs,
       word4 xs, word5 xs, word6 xs, word7 xs] :
       {l : List U32 // l.length = (8#usize).val})
  apply Subtype.ext
  exact hvals


theorem canonical_from_limbs_forward (xs : Array U32 8#usize)
    (hc : ∀ x∈xs.val,x.val<AspisV8R17.RawReducer.P) :
    ∃ body : Wide, finishFromLimbsCurrent xs=.ok (some body) := by
  have hc0 : (word0 xs).val<AspisV8R17.RawReducer.P := by
    apply hc
    apply List.getElem_mem
  have hc1 : (word1 xs).val<AspisV8R17.RawReducer.P := by
    apply hc
    apply List.getElem_mem
  have hc2 : (word2 xs).val<AspisV8R17.RawReducer.P := by
    apply hc
    apply List.getElem_mem
  have hc3 : (word3 xs).val<AspisV8R17.RawReducer.P := by
    apply hc
    apply List.getElem_mem
  have hc4 : (word4 xs).val<AspisV8R17.RawReducer.P := by
    apply hc
    apply List.getElem_mem
  have hc5 : (word5 xs).val<AspisV8R17.RawReducer.P := by
    apply hc
    apply List.getElem_mem
  have hc6 : (word6 xs).val<AspisV8R17.RawReducer.P := by
    apply hc
    apply List.getElem_mem
  have hc7 : (word7 xs).val<AspisV8R17.RawReducer.P := by
    apply hc
    apply List.getElem_mem
  have hm := AspisR1FastDotsN8WideFromLimbsABI.finishFromLimbsCurrent_make
    (word0 xs) (word1 xs) (word2 xs) (word3 xs)
    (word4 xs) (word5 xs) (word6 xs) (word7 xs)
    hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7
  rw [← array_eq_ordered_make xs] at hm
  exact ⟨_,hm⟩

theorem reduced_n8_pack_forward (base : Ops) (limbs : Array Std.U64 8#usize) :
    ∃ (values : Array U32 8#usize) (body : Wide),
      AspisR1FromFnP6Generated.arrayFromFnP6 8#usize
        (AspisR1FastDotsN8OutputForwardRootV1.InnerFn
          (AspisR1FastDotsCurrentM31OpsBinding.withCurrentM31ParserReducer base)) limbs = .ok values ∧
      (∀ x∈values.val,x.val<AspisV8R17.RawReducer.P) ∧
      finishFromLimbsCurrent values=.ok (some body) := by
  obtain ⟨values,ha,hc⟩ := AspisR1FastDotsN8OutputForwardRootV1.n8_array_forward base limbs
  obtain ⟨body,hb⟩ := canonical_from_limbs_forward values hc
  exact ⟨values,body,ha,hc,hb⟩

#print axioms array_eq_ordered_make
#print axioms canonical_from_limbs_forward
#print axioms reduced_n8_pack_forward
end AspisR1FastDotsN8PackForwardRootV1
