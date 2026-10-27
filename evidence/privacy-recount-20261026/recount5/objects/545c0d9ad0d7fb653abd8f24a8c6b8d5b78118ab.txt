import R0Z.PoseidonExtracted
import R0Z.WriterRefinePath
import R0Z.WriterRefineOccRow
import R0P.Poseidon

/-! Poseidon refinement, first step (DESIGN-BUILDER-MODEL §11.4 c).

`R0PoseidonCopy` is the Aeneas extraction of refine/poseidon (the
extraction-friendly copy of permute_optimized_with_trace, differentially
tested against production).  Here: the field operations, pow5, mat4, the
external linear layer and the single full round lift to R0P's
`poseidonPow5`, `poseidonMat4`, `poseidonExternalLinear`,
`poseidonFullRound`, for every u32 input state and constant row (all
reductions are `(u64 expression) % p`, so no canonicity is needed).  Loops
are proved by induction on the remaining iterations; no table or cell is
evaluated. -/
set_option autoImplicit false

namespace R0Z.PoseidonRefine
open Aeneas Aeneas.Std Result R0PoseidonCopy R0Z.WriterRefine

/-! ### Scalar plumbing -/

theorem u32lt (a : U32) : a.val < 4294967296 := by
  have h := a.hBounds
  rw [show UScalarTy.U32.numBits = 32 from rfl] at h
  exact h

theorem size64 : UScalar.size .U64 = 18446744073709551616 := by
  rw [UScalar.size_def]; rfl

theorem c64 (a : U32) : (UScalar.cast .U64 a).val = a.val := by
  rw [UScalar.cast_val_eq, show UScalarTy.U64.numBits = 64 from rfl]
  exact Nat.mod_eq_of_lt (by have := u32lt a; omega)

theorem c32 (x : U64) (h : x.val < 4294967296) : (UScalar.cast .U32 x).val = x.val := by
  rw [UScalar.cast_val_eq, show UScalarTy.U32.numBits = 32 from rfl]
  exact Nat.mod_eq_of_lt h

theorem add64v (x y : U64) (m n : Nat) (hx : x.val = m) (hy : y.val = n)
    (h : m + n < 18446744073709551616) : (U64.wrapping_add x y).val = m + n := by
  rw [U64.wrapping_add_val_eq, size64, hx, hy]; exact Nat.mod_eq_of_lt h

theorem mul64v (x y : U64) (m n : Nat) (hx : x.val = m) (hy : y.val = n)
    (h : m * n < 18446744073709551616) : (U64.wrapping_mul x y).val = m * n := by
  rw [U64.wrapping_mul_val_eq, size64, hx, hy]; exact Nat.mod_eq_of_lt h

theorem v2 : (2#u64 : U64).val = 2 := by simp
theorem v3 : (3#u64 : U64).val = 3 := by simp
theorem v4 : (4#usize : Usize).val = 4 := by simp
theorem v16 : (16#usize : Usize).val = 16 := by simp
theorem z0 : (0#usize : Usize).val = 0 := by simp
theorem z1 : (1#usize : Usize).val = 1 := by simp
theorem z2 : (2#usize : Usize).val = 2 := by simp
theorem z3 : (3#usize : Usize).val = 3 := by simp

theorem pval : (P : U32).val = 2147483647 := by rw [P]; simp
theorem p64 : (UScalar.cast .U64 P).val = 2147483647 := by rw [c64, pval]

theorem rem_ok {ty : UScalarTy} (x y : UScalar ty) (h : y.val ≠ 0) :
    (x % y : Result (UScalar ty)) = ok ⟨BitVec.umod x.bv y.bv⟩ := by
  show UScalar.rem x y = _
  unfold UScalar.rem
  rw [if_pos (by simpa using h)]

theorem umod_val {ty : UScalarTy} (x y : UScalar ty) :
    (⟨BitVec.umod x.bv y.bv⟩ : UScalar ty).val = x.val % y.val :=
  BitVec.toNat_umod

theorem remP (x : U64) :
    (x % UScalar.cast .U64 P : Result U64) = ok ⟨BitVec.umod x.bv (UScalar.cast .U64 P).bv⟩ :=
  rem_ok _ _ (by rw [p64]; omega)

/-! ### u64 shapes of the copy (no wrap) -/

theorem add2_val (a b : U32) :
    (U64.wrapping_add (UScalar.cast .U64 a) (UScalar.cast .U64 b)).val = a.val + b.val := by
  have := u32lt a; have := u32lt b
  exact add64v _ _ _ _ (c64 a) (c64 b) (by omega)

theorem mul2_val (a b : U32) :
    (U64.wrapping_mul (UScalar.cast .U64 a) (UScalar.cast .U64 b)).val = a.val * b.val := by
  have ha := u32lt a; have hb := u32lt b
  refine mul64v _ _ _ _ (c64 a) (c64 b) ?_
  calc a.val * b.val < 4294967296 * 4294967296 := Nat.mul_lt_mul'' ha hb
    _ = 18446744073709551616 := by norm_num

theorem sum4_val (a b c d : U32) :
    (U64.wrapping_add (U64.wrapping_add (U64.wrapping_add (UScalar.cast .U64 a) (UScalar.cast .U64 b))
      (UScalar.cast .U64 c)) (UScalar.cast .U64 d)).val = a.val + b.val + c.val + d.val := by
  have := u32lt a; have := u32lt b; have := u32lt c; have := u32lt d
  exact add64v _ _ _ _ (add64v _ _ _ _ (add64v _ _ _ _ (c64 a) (c64 b) (by omega)) (c64 c) (by omega))
    (c64 d) (by omega)

theorem mat_r0 (a b c d : U32) :
    (U64.wrapping_add (U64.wrapping_add (U64.wrapping_add (U64.wrapping_mul 2#u64 (UScalar.cast .U64 a))
      (U64.wrapping_mul 3#u64 (UScalar.cast .U64 b))) (UScalar.cast .U64 c)) (UScalar.cast .U64 d)).val
      = 2 * a.val + 3 * b.val + c.val + d.val := by
  have := u32lt a; have := u32lt b; have := u32lt c; have := u32lt d
  exact add64v _ _ _ _ (add64v _ _ _ _ (add64v _ _ _ _ (mul64v _ _ _ _ v2 (c64 a) (by omega))
    (mul64v _ _ _ _ v3 (c64 b) (by omega)) (by omega)) (c64 c) (by omega)) (c64 d) (by omega)

theorem mat_r1 (a b c d : U32) :
    (U64.wrapping_add (U64.wrapping_add (U64.wrapping_add (UScalar.cast .U64 a)
      (U64.wrapping_mul 2#u64 (UScalar.cast .U64 b))) (U64.wrapping_mul 3#u64 (UScalar.cast .U64 c)))
      (UScalar.cast .U64 d)).val = a.val + 2 * b.val + 3 * c.val + d.val := by
  have := u32lt a; have := u32lt b; have := u32lt c; have := u32lt d
  exact add64v _ _ _ _ (add64v _ _ _ _ (add64v _ _ _ _ (c64 a) (mul64v _ _ _ _ v2 (c64 b) (by omega))
    (by omega)) (mul64v _ _ _ _ v3 (c64 c) (by omega)) (by omega)) (c64 d) (by omega)

theorem mat_r2 (a b c d : U32) :
    (U64.wrapping_add (U64.wrapping_add (U64.wrapping_add (UScalar.cast .U64 a) (UScalar.cast .U64 b))
      (U64.wrapping_mul 2#u64 (UScalar.cast .U64 c))) (U64.wrapping_mul 3#u64 (UScalar.cast .U64 d))).val
      = a.val + b.val + 2 * c.val + 3 * d.val := by
  have := u32lt a; have := u32lt b; have := u32lt c; have := u32lt d
  exact add64v _ _ _ _ (add64v _ _ _ _ (add64v _ _ _ _ (c64 a) (c64 b) (by omega))
    (mul64v _ _ _ _ v2 (c64 c) (by omega)) (by omega)) (mul64v _ _ _ _ v3 (c64 d) (by omega)) (by omega)

theorem mat_r3 (a b c d : U32) :
    (U64.wrapping_add (U64.wrapping_add (U64.wrapping_add (U64.wrapping_mul 3#u64 (UScalar.cast .U64 a))
      (UScalar.cast .U64 b)) (UScalar.cast .U64 c)) (U64.wrapping_mul 2#u64 (UScalar.cast .U64 d))).val
      = 3 * a.val + b.val + c.val + 2 * d.val := by
  have := u32lt a; have := u32lt b; have := u32lt c; have := u32lt d
  exact add64v _ _ _ _ (add64v _ _ _ _ (add64v _ _ _ _ (mul64v _ _ _ _ v3 (c64 a) (by omega))
    (c64 b) (by omega)) (c64 c) (by omega)) (mul64v _ _ _ _ v2 (c64 d) (by omega)) (by omega)

/-! ### Lifting to K -/

variable {K : Type} [Field K]

/-- Lane `k` of a 16-lane state, lifted. -/
def liftN (s : Array U32 16#usize) (k : Nat) : K := liftU (s.val[k]!)

/-- The lifted state as R0P's `Fin 16 → K`. -/
def liftA (s : Array U32 16#usize) : Fin 16 → K := fun i => liftU (s.val[i.val]!)

/-- R0P's group-`g` matrix output `c`, read through `liftN`. -/
def PM (s : Array U32 16#usize) (g c : Fin 4) : K :=
  R0P.poseidonMat4 (fun lane : Fin 4 => liftN s (4 * g.val + lane.val)) c

variable [CharP K 0x7fffffff]

theorem cast_mod (n : Nat) : ((n % 2147483647 : Nat) : K) = (n : K) := by
  conv_rhs => rw [← Nat.mod_add_div n 2147483647]
  rw [Nat.cast_add, Nat.cast_mul, CharP.cast_eq_zero K 0x7fffffff, zero_mul, add_zero]

theorem liftmod (x : U64) :
    liftU (K := K) (UScalar.cast .U32 (⟨BitVec.umod x.bv (UScalar.cast .U64 P).bv⟩ : U64)) =
      ((x.val : Nat) : K) := by
  unfold liftU
  have hm : (⟨BitVec.umod x.bv (UScalar.cast .U64 P).bv⟩ : U64).val = x.val % 2147483647 := by
    rw [umod_val, p64]
  have hlt : x.val % 2147483647 < 2147483647 := Nat.mod_lt _ (by omega)
  rw [c32 _ (by rw [hm]; omega), hm, cast_mod]

theorem add_lift (a b : U32) :
    ∃ z, m31_add a b = ok z ∧ liftU (K := K) z = liftU a + liftU b := by
  rw [m31_add]
  simp only [lift, bind_tc_ok, remP]
  refine ⟨_, rfl, ?_⟩
  rw [liftmod, add2_val]
  unfold liftU
  push_cast
  rfl

theorem mul_lift (a b : U32) :
    ∃ z, m31_mul a b = ok z ∧ liftU (K := K) z = liftU a * liftU b := by
  rw [m31_mul]
  simp only [lift, bind_tc_ok, remP]
  refine ⟨_, rfl, ?_⟩
  rw [liftmod, mul2_val]
  unfold liftU
  push_cast
  rfl

theorem pow5_lift (x : U32) :
    ∃ z, pow5 x = ok z ∧ liftU (K := K) z = R0P.poseidonPow5 (liftU x) := by
  obtain ⟨s, hs, hsv⟩ := mul_lift (K := K) x x
  obtain ⟨t, ht, htv⟩ := mul_lift (K := K) s s
  obtain ⟨u, hu, huv⟩ := mul_lift (K := K) t x
  refine ⟨u, ?_, ?_⟩
  · rw [pow5, hs]
    simp only [bind_tc_ok]
    rw [ht]
    simp only [bind_tc_ok]
    exact hu
  · rw [huv, htv, hsv]
    rfl

/-! ### mat4 -/

theorem mk4 (x0 x1 x2 x3 : U32) (h : [x0, x1, x2, x3].length = (4#usize : Usize).val) :
    (Array.make 4#usize [x0, x1, x2, x3] h).val = [x0, x1, x2, x3] := rfl
theorem gl0 (x0 x1 x2 x3 : U32) : ([x0, x1, x2, x3] : List U32)[0]! = x0 := rfl
theorem gl1 (x0 x1 x2 x3 : U32) : ([x0, x1, x2, x3] : List U32)[1]! = x1 := rfl
theorem gl2 (x0 x1 x2 x3 : U32) : ([x0, x1, x2, x3] : List U32)[2]! = x2 := rfl
theorem gl3 (x0 x1 x2 x3 : U32) : ([x0, x1, x2, x3] : List U32)[3]! = x3 := rfl

theorem pm0 (v : Fin 4 → K) :
    R0P.poseidonMat4 v 0 = ((v 0 + v 1) + (v 2 + v 3) + v 1) + (v 0 + v 1) := rfl
theorem pm1 (v : Fin 4 → K) :
    R0P.poseidonMat4 v 1 = ((v 0 + v 1) + (v 2 + v 3) + v 1) + (v 2 + v 2) := rfl
theorem pm2 (v : Fin 4 → K) :
    R0P.poseidonMat4 v 2 = ((v 0 + v 1) + (v 2 + v 3) + v 3) + (v 2 + v 3) := rfl
theorem pm3 (v : Fin 4 → K) :
    R0P.poseidonMat4 v 3 = ((v 0 + v 1) + (v 2 + v 3) + v 3) + (v 0 + v 0) := rfl

theorem mat4_lift (a b c d : U32) (v : Fin 4 → K) (ha : liftU a = v 0) (hb : liftU b = v 1)
    (hc : liftU c = v 2) (hd : liftU d = v 3) :
    ∃ m, mat4 a b c d = ok m ∧
      liftU (m.val[0]!) = R0P.poseidonMat4 v 0 ∧ liftU (m.val[1]!) = R0P.poseidonMat4 v 1 ∧
      liftU (m.val[2]!) = R0P.poseidonMat4 v 2 ∧ liftU (m.val[3]!) = R0P.poseidonMat4 v 3 := by
  rw [mat4]
  simp only [lift, bind_tc_ok, remP]
  refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩
  · rw [mk4, gl0, liftmod, mat_r0, pm0, ← ha, ← hb, ← hc, ← hd]
    unfold liftU; push_cast; ring
  · rw [mk4, gl1, liftmod, mat_r1, pm1, ← ha, ← hb, ← hc, ← hd]
    unfold liftU; push_cast; ring
  · rw [mk4, gl2, liftmod, mat_r2, pm2, ← ha, ← hb, ← hc, ← hd]
    unfold liftU; push_cast; ring
  · rw [mk4, gl3, liftmod, mat_r3, pm3, ← ha, ← hb, ← hc, ← hd]
    unfold liftU; push_cast; ring

/-! ### Four consecutive writes -/

theorem set4 {n : Usize} (v : Array U32 n) (i0 i1 i2 i3 : Usize) (x0 x1 x2 x3 : U32) (b : Nat)
    (h0 : i0.val = b) (h1 : i1.val = b + 1) (h2 : i2.val = b + 2) (h3 : i3.val = b + 3)
    (hb : b + 3 < n.val) :
    ((((v.set i0 x0).set i1 x1).set i2 x2).set i3 x3).val[b]! = x0 ∧
    ((((v.set i0 x0).set i1 x1).set i2 x2).set i3 x3).val[b + 1]! = x1 ∧
    ((((v.set i0 x0).set i1 x1).set i2 x2).set i3 x3).val[b + 2]! = x2 ∧
    ((((v.set i0 x0).set i1 x1).set i2 x2).set i3 x3).val[b + 3]! = x3 ∧
    ∀ k, k < b → ((((v.set i0 x0).set i1 x1).set i2 x2).set i3 x3).val[k]! = v.val[k]! := by
  have e3 := set_get' (((v.set i0 x0).set i1 x1).set i2 x2) i3 x3 (by omega)
  have e2 := set_get' ((v.set i0 x0).set i1 x1) i2 x2 (by omega)
  have e1 := set_get' (v.set i0 x0) i1 x1 (by omega)
  have e0 := set_get' v i0 x0 (by omega)
  refine ⟨?_, ?_, ?_, ?_, fun k hk => ?_⟩ <;>
    (rw [e3, e2, e1, e0, h0, h1, h2, h3]; split_ifs <;> first | rfl | omega)

/-! ### The S-box loop -/

theorem sbox_loop (s c : Array U32 16#usize) :
    ∀ (n : Nat) (i : Usize) (out : Array U32 16#usize), i.val + n = 16 →
      ∃ o, sbox_full_loop s c out i = ok o ∧ ∀ k, k < 16 →
        (i.val ≤ k → liftU (K := K) (o.val[k]!) = R0P.poseidonPow5 (liftN s k + liftN c k)) ∧
        (k < i.val → o.val[k]! = out.val[k]!)
  | 0, i, out, h => by
      refine ⟨out, ?_, fun k hk => ⟨fun h' => absurd h' (by omega), fun _ => rfl⟩⟩
      rw [sbox_full_loop, if_neg (by rw [UScalar.lt_equiv]; scalar_tac)]
  | n + 1, i, out, h => by
      have hlt : i < 16#usize := by rw [UScalar.lt_equiv]; scalar_tac
      have hb : i.val < (16#usize).val := by rw [v16]; omega
      have hi1 : (Usize.wrapping_add i 1#usize).val = i.val + 1 := uadd _ _ (by scalar_tac)
      obtain ⟨z, hz, hzv⟩ := add_lift (K := K) (s.val[i.val]!) (c.val[i.val]!)
      obtain ⟨y, hy, hyv⟩ := pow5_lift (K := K) z
      obtain ⟨o, ho, hov⟩ := sbox_loop s c n (Usize.wrapping_add i 1#usize) (out.set i y)
        (by rw [hi1]; omega)
      refine ⟨o, ?_, fun k hk => ⟨fun hik => ?_, fun hki => ?_⟩⟩
      · rw [sbox_full_loop, if_pos hlt]
        simp only [lift, bind_tc_ok, index_ok s i hb, index_ok c i hb, hz, hy, update_ok out i y hb]
        exact ho
      · by_cases e : k = i.val
        · subst e
          rw [(hov i.val hk).2 (by rw [hi1]; omega), set_get' out i y hb i.val, if_pos rfl, hyv, hzv]
          rfl
        · exact (hov k hk).1 (by rw [hi1]; omega)
      · rw [(hov k hk).2 (by rw [hi1]; omega), set_get' out i y hb k, if_neg (by omega)]

/-! ### The external layer -/

theorem groups_loop (s : Array U32 16#usize) :
    ∀ (n : Nat) (g : Usize) (out : Array U32 16#usize), g.val + n = 4 →
      ∃ o, ext_groups_loop s out g = ok o ∧
        (∀ (g' c : Nat) (hg : g' < 4) (hc : c < 4), g.val ≤ g' →
          liftU (K := K) (o.val[4 * g' + c]!) = PM s ⟨g', hg⟩ ⟨c, hc⟩) ∧
        (∀ k, k < 4 * g.val → o.val[k]! = out.val[k]!)
  | 0, g, out, h => by
      refine ⟨out, ?_, fun g' c hg hc h' => absurd h' (by omega), fun _ _ => rfl⟩
      rw [ext_groups_loop, if_neg (by rw [UScalar.lt_equiv]; scalar_tac)]
  | n + 1, g, out, h => by
      have hlt : g < 4#usize := by rw [UScalar.lt_equiv]; scalar_tac
      have h4 : (Usize.wrapping_mul 4#usize g).val = 4 * g.val := by
        rw [umul _ _ (by rw [v4]; omega), v4]
      have h1 : (Usize.wrapping_add (Usize.wrapping_mul 4#usize g) 1#usize).val = 4 * g.val + 1 := by
        rw [uadd _ _ (by rw [h4, z1]; omega), h4, z1]
      have h2 : (Usize.wrapping_add (Usize.wrapping_mul 4#usize g) 2#usize).val = 4 * g.val + 2 := by
        rw [uadd _ _ (by rw [h4, z2]; omega), h4, z2]
      have h3 : (Usize.wrapping_add (Usize.wrapping_mul 4#usize g) 3#usize).val = 4 * g.val + 3 := by
        rw [uadd _ _ (by rw [h4, z3]; omega), h4, z3]
      have hg1 : (Usize.wrapping_add g 1#usize).val = g.val + 1 := uadd _ _ (by scalar_tac)
      have hb0 : (Usize.wrapping_mul 4#usize g).val < (16#usize).val := by rw [h4, v16]; omega
      have hb1 : (Usize.wrapping_add (Usize.wrapping_mul 4#usize g) 1#usize).val < (16#usize).val := by
        rw [h1, v16]; omega
      have hb2 : (Usize.wrapping_add (Usize.wrapping_mul 4#usize g) 2#usize).val < (16#usize).val := by
        rw [h2, v16]; omega
      have hb3 : (Usize.wrapping_add (Usize.wrapping_mul 4#usize g) 3#usize).val < (16#usize).val := by
        rw [h3, v16]; omega
      obtain ⟨m, hm, hm0, hm1, hm2, hm3⟩ := mat4_lift (K := K)
        (s.val[(Usize.wrapping_mul 4#usize g).val]!)
        (s.val[(Usize.wrapping_add (Usize.wrapping_mul 4#usize g) 1#usize).val]!)
        (s.val[(Usize.wrapping_add (Usize.wrapping_mul 4#usize g) 2#usize).val]!)
        (s.val[(Usize.wrapping_add (Usize.wrapping_mul 4#usize g) 3#usize).val]!)
        (fun lane : Fin 4 => liftN s (4 * g.val + lane.val))
        (by rw [h4]; rfl) (by rw [h1]; rfl) (by rw [h2]; rfl) (by rw [h3]; rfl)
      have S := set4 out (Usize.wrapping_mul 4#usize g)
        (Usize.wrapping_add (Usize.wrapping_mul 4#usize g) 1#usize)
        (Usize.wrapping_add (Usize.wrapping_mul 4#usize g) 2#usize)
        (Usize.wrapping_add (Usize.wrapping_mul 4#usize g) 3#usize)
        (m.val[0]!) (m.val[1]!) (m.val[2]!) (m.val[3]!) (4 * g.val) h4 h1 h2 h3 (by rw [v16]; omega)
      obtain ⟨o, ho, hoG, hoF⟩ := groups_loop s n (Usize.wrapping_add g 1#usize)
        ((((out.set (Usize.wrapping_mul 4#usize g) (m.val[0]!)).set
          (Usize.wrapping_add (Usize.wrapping_mul 4#usize g) 1#usize) (m.val[1]!)).set
          (Usize.wrapping_add (Usize.wrapping_mul 4#usize g) 2#usize) (m.val[2]!)).set
          (Usize.wrapping_add (Usize.wrapping_mul 4#usize g) 3#usize) (m.val[3]!))
        (by rw [hg1]; omega)
      refine ⟨o, ?_, fun g' c hg hc hle => ?_, fun k hk => ?_⟩
      · rw [ext_groups_loop, if_pos hlt]
        simp only [lift, bind_tc_ok, index_ok s _ hb0, index_ok s _ hb1, index_ok s _ hb2,
          index_ok s _ hb3, hm, index_ok m 0#usize (by rw [z0, v4]; omega),
          index_ok m 1#usize (by rw [z1, v4]; omega), index_ok m 2#usize (by rw [z2, v4]; omega),
          index_ok m 3#usize (by rw [z3, v4]; omega), update_ok _ _ _ hb0, update_ok _ _ _ hb1,
          update_ok _ _ _ hb2, update_ok _ _ _ hb3, z0, z1, z2, z3]
        exact ho
      · by_cases e : g' = g.val
        · subst e
          rw [hoF _ (by rw [hg1]; omega)]
          have hc' : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by omega
          rcases hc' with rfl | rfl | rfl | rfl
          · rw [show 4 * g.val + 0 = 4 * g.val from rfl, S.1]; exact hm0
          · rw [S.2.1]; exact hm1
          · rw [S.2.2.1]; exact hm2
          · rw [S.2.2.2.1]; exact hm3
        · exact hoG g' c hg hc (by rw [hg1]; omega)
      · rw [hoF k (by rw [hg1]; omega)]
        exact S.2.2.2.2 k hk

theorem sums_loop (gr : Array U32 16#usize) :
    ∀ (n : Nat) (col : Usize) (sums : Array U32 4#usize), col.val + n = 4 →
      ∃ o, ext_sums_loop gr sums col = ok o ∧ ∀ c, c < 4 →
        (col.val ≤ c → liftU (K := K) (o.val[c]!) =
          liftN gr c + liftN gr (4 + c) + liftN gr (8 + c) + liftN gr (12 + c)) ∧
        (c < col.val → o.val[c]! = sums.val[c]!)
  | 0, col, sums, h => by
      refine ⟨sums, ?_, fun c hc => ⟨fun h' => absurd h' (by omega), fun _ => rfl⟩⟩
      rw [ext_sums_loop, if_neg (by rw [UScalar.lt_equiv]; scalar_tac)]
  | n + 1, col, sums, h => by
      have hlt : col < 4#usize := by rw [UScalar.lt_equiv]; scalar_tac
      have hb : col.val < (16#usize).val := by rw [v16]; omega
      have hbs : col.val < (4#usize).val := by rw [v4]; omega
      have hc4 : (Usize.wrapping_add 4#usize col).val = 4 + col.val := by
        rw [uadd _ _ (by rw [v4]; omega), v4]
      have hc8 : (Usize.wrapping_add 8#usize col).val = 8 + col.val := by
        rw [uadd _ _ (by rw [show (8#usize : Usize).val = 8 by simp]; omega),
          show (8#usize : Usize).val = 8 by simp]
      have hc12 : (Usize.wrapping_add 12#usize col).val = 12 + col.val := by
        rw [uadd _ _ (by rw [show (12#usize : Usize).val = 12 by simp]; omega),
          show (12#usize : Usize).val = 12 by simp]
      have hb4 : (Usize.wrapping_add 4#usize col).val < (16#usize).val := by rw [hc4, v16]; omega
      have hb8 : (Usize.wrapping_add 8#usize col).val < (16#usize).val := by rw [hc8, v16]; omega
      have hb12 : (Usize.wrapping_add 12#usize col).val < (16#usize).val := by rw [hc12, v16]; omega
      have hcol1 : (Usize.wrapping_add col 1#usize).val = col.val + 1 := uadd _ _ (by scalar_tac)
      have step : ∃ X : U32, ext_sums_loop gr sums col =
          ext_sums_loop gr (sums.set col X) (Usize.wrapping_add col 1#usize) ∧
          liftU (K := K) X = liftN gr col.val + liftN gr (4 + col.val) + liftN gr (8 + col.val) +
            liftN gr (12 + col.val) := by
        rw [ext_sums_loop, if_pos hlt]
        simp only [lift, bind_tc_ok, index_ok gr col hb, index_ok gr _ hb4, index_ok gr _ hb8,
          index_ok gr _ hb12, remP, update_ok sums col _ hbs]
        refine ⟨_, rfl, ?_⟩
        rw [liftmod, sum4_val, hc4, hc8, hc12]
        unfold liftN liftU
        push_cast
        rfl
      obtain ⟨X, hX, hXv⟩ := step
      have hs := set_get' sums col X hbs
      obtain ⟨o, ho, hov⟩ := sums_loop gr n (Usize.wrapping_add col 1#usize) (sums.set col X)
        (by rw [hcol1]; omega)
      refine ⟨o, by rw [hX]; exact ho, fun c hc => ⟨fun hle => ?_, fun hlt' => ?_⟩⟩
      · by_cases e : c = col.val
        · subst e
          rw [(hov col.val hc).2 (by rw [hcol1]; omega), hs, if_pos rfl]
          exact hXv
        · exact (hov c hc).1 (by rw [hcol1]; omega)
      · rw [(hov c hc).2 (by rw [hcol1]; omega), hs, if_neg (by omega)]

theorem add_loop (gr : Array U32 16#usize) (sums : Array U32 4#usize) :
    ∀ (n : Nat) (i : Usize) (out : Array U32 16#usize), i.val + n = 16 →
      ∃ o, ext_add_loop gr sums out i = ok o ∧ ∀ k, k < 16 →
        (i.val ≤ k → liftU (K := K) (o.val[k]!) = liftN gr k + liftU (sums.val[k % 4]!)) ∧
        (k < i.val → o.val[k]! = out.val[k]!)
  | 0, i, out, h => by
      refine ⟨out, ?_, fun k hk => ⟨fun h' => absurd h' (by omega), fun _ => rfl⟩⟩
      rw [ext_add_loop, if_neg (by rw [UScalar.lt_equiv]; scalar_tac)]
  | n + 1, i, out, h => by
      have hlt : i < 16#usize := by rw [UScalar.lt_equiv]; scalar_tac
      have hb : i.val < (16#usize).val := by rw [v16]; omega
      have hi1 : (Usize.wrapping_add i 1#usize).val = i.val + 1 := uadd _ _ (by scalar_tac)
      have hr : (⟨BitVec.umod i.bv (4#usize : Usize).bv⟩ : Usize).val = i.val % 4 := by
        rw [umod_val, v4]
      have hrb : (⟨BitVec.umod i.bv (4#usize : Usize).bv⟩ : Usize).val < (4#usize).val := by
        rw [hr, v4]; omega
      obtain ⟨z, hz, hzv⟩ := add_lift (K := K) (gr.val[i.val]!)
        (sums.val[(⟨BitVec.umod i.bv (4#usize : Usize).bv⟩ : Usize).val]!)
      obtain ⟨o, ho, hov⟩ := add_loop gr sums n (Usize.wrapping_add i 1#usize) (out.set i z)
        (by rw [hi1]; omega)
      refine ⟨o, ?_, fun k hk => ⟨fun hik => ?_, fun hki => ?_⟩⟩
      · rw [ext_add_loop, if_pos hlt]
        simp only [lift, bind_tc_ok, index_ok gr i hb, rem_ok i 4#usize (by rw [v4]; omega),
          index_ok sums _ hrb, hz, update_ok out i z hb]
        exact ho
      · by_cases e : k = i.val
        · subst e
          rw [(hov i.val hk).2 (by rw [hi1]; omega), set_get' out i z hb i.val, if_pos rfl, hzv, hr]
          rfl
        · exact (hov k hk).1 (by rw [hi1]; omega)
      · rw [(hov k hk).2 (by rw [hi1]; omega), set_get' out i z hb k, if_neg (by omega)]

theorem ext_unfold (s : Array U32 16#usize) (i : Fin 16) :
    R0P.poseidonExternalLinear (liftA (K := K) s) i =
      PM s ⟨i.val / 4, by have := i.isLt; omega⟩ ⟨i.val % 4, by have := i.isLt; omega⟩ +
        ((((0 + PM s ⟨0, by decide⟩ ⟨i.val % 4, by have := i.isLt; omega⟩) +
          PM s ⟨1, by decide⟩ ⟨i.val % 4, by have := i.isLt; omega⟩) +
          PM s ⟨2, by decide⟩ ⟨i.val % 4, by have := i.isLt; omega⟩) +
          PM s ⟨3, by decide⟩ ⟨i.val % 4, by have := i.isLt; omega⟩) := rfl

/-- The external linear layer of the copy lifts to R0P's `poseidonExternalLinear`. -/
theorem external_lift (s : Array U32 16#usize) :
    ∃ t, external_linear s = ok t ∧
      ∀ i : Fin 16, liftU (K := K) (t.val[i.val]!) = R0P.poseidonExternalLinear (liftA s) i := by
  obtain ⟨gr, hgr, hG, -⟩ := groups_loop (K := K) s 4 0#usize (Array.repeat 16#usize 0#u32)
    (by rw [z0])
  obtain ⟨sm, hsm, hS⟩ := sums_loop (K := K) gr 4 0#usize (Array.repeat 4#usize 0#u32) (by rw [z0])
  obtain ⟨t, ht, hT⟩ := add_loop (K := K) gr sm 16 0#usize (Array.repeat 16#usize 0#u32)
    (by rw [z0])
  refine ⟨t, ?_, fun i => ?_⟩
  · simp only [external_linear, ext_groups, ext_sums, ext_add, hgr, hsm, ht, bind_tc_ok]
  · have hi := i.isLt
    rw [(hT i.val hi).1 (by rw [z0]; omega), (hS (i.val % 4) (by omega)).1 (by rw [z0]; omega),
      ext_unfold]
    have G := hG (i.val / 4) (i.val % 4) (by omega) (by omega) (z0.trans_le (Nat.zero_le _))
    have G0 := hG 0 (i.val % 4) (by omega) (by omega) (z0.trans_le (Nat.zero_le _))
    have G1 := hG 1 (i.val % 4) (by omega) (by omega) (z0.trans_le (Nat.zero_le _))
    have G2 := hG 2 (i.val % 4) (by omega) (by omega) (z0.trans_le (Nat.zero_le _))
    have G3 := hG 3 (i.val % 4) (by omega) (by omega) (z0.trans_le (Nat.zero_le _))
    rw [Nat.div_add_mod] at G
    rw [show 4 * 0 + i.val % 4 = i.val % 4 by omega] at G0
    rw [show 4 * 1 + i.val % 4 = 4 + i.val % 4 by omega] at G1
    rw [show 4 * 2 + i.val % 4 = 8 + i.val % 4 by omega] at G2
    rw [show 4 * 3 + i.val % 4 = 12 + i.val % 4 by omega] at G3
    rw [← G, ← G0, ← G1, ← G2, ← G3]
    unfold liftN
    ring

/-- **Single full round.**  For every u32 state `s` and constant row `c`, the
extracted copy's `full_round` returns `ok t` and every lane of `t` lifts to
R0P's `poseidonFullRound` of the lifted state and constants. -/
theorem full_round_lift (s c : Array U32 16#usize) :
    ∃ t, full_round s c = ok t ∧
      ∀ i : Fin 16, liftU (K := K) (t.val[i.val]!) = R0P.poseidonFullRound (liftA s) (liftA c) i := by
  obtain ⟨b, hb, hbv⟩ := sbox_loop (K := K) s c 16 0#usize (Array.repeat 16#usize 0#u32) (by rw [z0])
  obtain ⟨t, ht, htv⟩ := external_lift (K := K) b
  refine ⟨t, ?_, fun i => ?_⟩
  · simp only [full_round, sbox_full, hb, bind_tc_ok, ht]
  · rw [htv i]
    have hfun : liftA (K := K) b = fun lane => R0P.poseidonPow5 (liftA s lane + liftA c lane) :=
      funext fun lane => (hbv lane.val lane.isLt).1 (by rw [z0]; omega)
    rw [hfun]
    rfl

end R0Z.PoseidonRefine

#print axioms R0Z.PoseidonRefine.add_lift
#print axioms R0Z.PoseidonRefine.mul_lift
#print axioms R0Z.PoseidonRefine.pow5_lift
#print axioms R0Z.PoseidonRefine.mat4_lift
#print axioms R0Z.PoseidonRefine.external_lift
#print axioms R0Z.PoseidonRefine.full_round_lift
