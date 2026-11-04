import NFO_HeaderWrites
set_option autoImplicit false
namespace NFO_FlatMapInjective

theorem uniform {A B : Type} (encode : A → List B) (width : Nat)
    (positive : 0 < width) (size : ∀ a, (encode a).length = width)
    (injective : Function.Injective encode) :
    Function.Injective (fun xs : List A => xs.flatMap encode) := by
  have take_word (a : A) : (encode a).take width = encode a :=
    List.take_of_length_le (by rw [size])
  intro xs ys same
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons b tail =>
      have lengths := congrArg List.length same
      simp only [List.flatMap_nil,List.flatMap_cons,List.length_append,List.length_nil,size] at lengths
      omega
  | cons a tail ih =>
    cases ys with
    | nil =>
      have lengths := congrArg List.length same
      simp only [List.flatMap_nil,List.flatMap_cons,List.length_append,List.length_nil,size] at lengths
      omega
    | cons b rest =>
      have head := congrArg (List.take width) same
      have words : encode a = encode b := by
        simpa [List.flatMap_cons,List.take_append,size,take_word] using head
      have ab := injective words
      subst b
      have dropped := congrArg (List.drop width) same
      have tails : tail.flatMap encode = rest.flatMap encode := by
        simpa [List.flatMap_cons,List.drop_append,size] using dropped
      rw [ih tails]
#print axioms uniform
end NFO_FlatMapInjective
