import R1Z.ProverCommitPublicSuccess34

/-! Composition against the actual generated twenty-row frontier function.
The auxiliary chain is connected to that function by frontier_eq_chain; it is
not assumed to model the Rust source. Successful return is the only premise. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow

namespace AspisR1PublicSerializer.Frontier431
open FieldsRefinement431 Success431
open pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes

abbrev Frontier := Array (Array Field 8#usize) 20#usize

def thenCheck (m : Result (Status × ByteVec))
    (k : ByteVec → Result (Status × ByteVec)) : Result (Status × ByteVec) := do
  let (r, out) ← m
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | .Continue _ => k out
  | .Break residual =>
    let r' ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Unit (core.convert.FromSame PublicError) residual
    ok (r', out)

theorem thenCheck_success (m : Result (Status × ByteVec))
    (k : ByteVec → Result (Status × ByteVec)) (out' : ByteVec)
    (h : thenCheck m k = ok (.Ok (), out')) :
    ∃ out, m = ok (.Ok (), out) ∧ k out = ok (.Ok (), out') := by
  cases m with
  | fail e => simp [thenCheck] at h
  | div => simp [thenCheck] at h
  | ok r =>
    rcases r with ⟨status, out⟩
    cases status with
    | Err e =>
      simp [thenCheck, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame] at h
    | Ok u =>
      cases u
      exact ⟨out, rfl, by simpa [thenCheck,
        core.result.Result.Insts.CoreOpsTry.branch] using h⟩

def chain : List (Slice Field) → ByteVec → Result (Status × ByteVec)
  | [], out => ok (.Ok (), out)
  | s :: ss, out => thenCheck (fields out s) (chain ss)

theorem chain_success (ss : List (Slice Field)) (out out' : ByteVec)
    (h : chain ss out = ok (.Ok (), out')) :
    canonical (ss.flatMap (fun s => s.val)) ∧
      out'.val = out.val ++ encodeWords (ss.flatMap (fun s => s.val)) := by
  induction ss generalizing out with
  | nil =>
    have heq : out = out' := congrArg Prod.snd (Result.ok.inj h)
    subst out'
    simp [canonical, encodeWords]
  | cons s ss ih =>
    obtain ⟨out1, hf, ht⟩ := thenCheck_success _ _ out' h
    have hs := fields_success out out1 s hf
    have hss := ih out1 ht
    constructor
    · intro x hx
      simp only [List.flatMap_cons, List.mem_append] at hx
      exact hx.elim (hs.1 x) (hss.1 x)
    · rw [hss.2, hs.2]
      simp only [List.flatMap_cons, encodeWords, List.flatMap_append, List.append_assoc]

def row (values : Frontier) (i : Fin 20) : Slice Field :=
  Array.to_slice (values.val[i.val]'(by simpa [values.property] using i.isLt))

theorem index20 (values : Frontier) (i : Usize) (hi : i.val < 20) :
    Array.index_usize values i = ok (values.val[i.val]'(by
      simpa [values.property] using hi)) := by
  obtain ⟨x, hx, heq⟩ := WP.spec_imp_exists
    (Array.index_usize_spec values i (by simpa [Array.length, values.property] using hi))
  simpa only [heq] using hx

def rows (values : Frontier) : List (Slice Field) :=
  [ row values ⟨0, by decide⟩,
    row values ⟨1, by decide⟩,
    row values ⟨2, by decide⟩,
    row values ⟨3, by decide⟩,
    row values ⟨4, by decide⟩,
    row values ⟨5, by decide⟩,
    row values ⟨6, by decide⟩,
    row values ⟨7, by decide⟩,
    row values ⟨8, by decide⟩,
    row values ⟨9, by decide⟩,
    row values ⟨10, by decide⟩,
    row values ⟨11, by decide⟩,
    row values ⟨12, by decide⟩,
    row values ⟨13, by decide⟩,
    row values ⟨14, by decide⟩,
    row values ⟨15, by decide⟩,
    row values ⟨16, by decide⟩,
    row values ⟨17, by decide⟩,
    row values ⟨18, by decide⟩,
    row values ⟨19, by decide⟩ ]

theorem frontier_eq_chain (out : ByteVec) (values : Frontier) :
    frontier out values = chain (rows values) out := by
  have h0 := index20 values 0#usize (by decide)
  have h1 := index20 values 1#usize (by decide)
  have h2 := index20 values 2#usize (by decide)
  have h3 := index20 values 3#usize (by decide)
  have h4 := index20 values 4#usize (by decide)
  have h5 := index20 values 5#usize (by decide)
  have h6 := index20 values 6#usize (by decide)
  have h7 := index20 values 7#usize (by decide)
  have h8 := index20 values 8#usize (by decide)
  have h9 := index20 values 9#usize (by decide)
  have h10 := index20 values 10#usize (by decide)
  have h11 := index20 values 11#usize (by decide)
  have h12 := index20 values 12#usize (by decide)
  have h13 := index20 values 13#usize (by decide)
  have h14 := index20 values 14#usize (by decide)
  have h15 := index20 values 15#usize (by decide)
  have h16 := index20 values 16#usize (by decide)
  have h17 := index20 values 17#usize (by decide)
  have h18 := index20 values 18#usize (by decide)
  have h19 := index20 values 19#usize (by decide)
  simp only [frontier, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, lift, bind_tc_ok]
  rfl

theorem frontier_success (out out' : ByteVec) (values : Frontier)
    (h : frontier out values = ok (.Ok (), out')) :
    canonical ((rows values).flatMap (fun s => s.val)) ∧
      out'.val = out.val ++ encodeWords ((rows values).flatMap (fun s => s.val)) := by
  rw [frontier_eq_chain] at h
  exact chain_success _ out out' h

#print axioms thenCheck_success
#print axioms chain_success
#print axioms frontier_eq_chain
#print axioms frontier_success

end AspisR1PublicSerializer.Frontier431
