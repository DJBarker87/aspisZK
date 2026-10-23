import S9TwoFoldProductModelV1
set_option autoImplicit false
noncomputable section
namespace AspisR1S9SymbolicRowTransportV1
open scoped BigOperators
variable {K : Type} [Field K]

def shape (alpha : K) (a : Fin 4 → K) (q : K) : K :=
  (((((0 : K)+alpha^0*a 0)+alpha^3*a 1)+alpha^2*a 2)+alpha^1*a 3)*q

theorem factor_shape (alpha : K) (a : Fin 4 → K) :
    AspisR1S9TwoFoldProductModelV1.factor alpha a=
      shape alpha a AspisR1.RoundPairing.quarter := rfl

theorem shape_quarter_congr (alpha : K) (a : Fin 4 → K) (q r : K) (h : q=r) :
    shape alpha a q=shape alpha a r := congrArg (shape alpha a) h

theorem mapped_triple {A B : Type} [CommSemiring A] [CommSemiring B]
    (iota : A →+* B) (x y z : A) : iota (x*y*z)=(iota x*iota y)*iota z := by
  exact (map_mul iota (x*y) z).trans
    (congrArg (fun t : B => t*iota z) (map_mul iota x y))

theorem dot_scaled_transport {n : Nat} (f c w : Fin n → K) (s : K)
    (h : ∀ i,w i=s*c i) :
    AspisR1.RoundPairing.dot f w=s*∑ i : Fin n,f i*c i := by
  unfold AspisR1.RoundPairing.dot
  calc
    _ = ∑ i : Fin n,f i*(s*c i) :=
      Finset.sum_congr rfl (fun i _ => congrArg (fun v : K => f i*v) (h i))
    _ = _ := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => mul_left_comm _ _ _)

#print axioms factor_shape
#print axioms shape_quarter_congr
#print axioms mapped_triple
#print axioms dot_scaled_transport
end AspisR1S9SymbolicRowTransportV1
end
