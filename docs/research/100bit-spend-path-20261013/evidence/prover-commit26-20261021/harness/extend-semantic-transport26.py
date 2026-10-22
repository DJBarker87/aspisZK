from pathlib import Path
p=Path('docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitSemanticTransport26.lean')
s=p.read_text();a=s.index('\n#print axioms zero_test')
S='AspisR1SimSemantic20';C='AspisR1CircleCaller25'
extra=f'''
theorem fields_bounded (remaining : Nat) (row : U8) (payload : alloc.vec.Vec U8) (value : Usize)
    (bound : payload.val.length < 32*(remaining+1)) :
    mapR errorMap ({S}.r1_wire.fields20.validate row payload value) =
      {C}.r1_wire.fields20.validate row payload value := by
  induction remaining generalizing payload value with
  | zero =>
    have short : alloc.vec.Vec.len payload < 32#usize := by change payload.val.length<32;omega
    rw [{S}.r1_wire.fields20.validate,{C}.r1_wire.fields20.validate]
    simp only [short,if_true,map_ok,errorMap]
  | succ n ih =>
    rw [{S}.r1_wire.fields20.validate,{C}.r1_wire.fields20.validate]
    by_cases short : alloc.vec.Vec.len payload < 32#usize
    · simp only [short,if_true,map_ok,errorMap]
    · simp only [short,if_false]
      have long : 32 ≤ payload.val.length := by change ¬payload.val.length<32 at short;omega
      have tailEq := ProverCommitFields20.drop_total payload long
      have tailBound : (Slice.drop payload 32#usize).val.length < 32*(n+1) := by
        simp only [Slice.getElem!_val_drop,List.length_drop]
        change payload.val.length-32<32*(n+1)
        omega
      have tailRec := ih (Slice.drop payload 32#usize) (Usize.wrapping_add value 1#usize) tailBound
      cases hp : alloc.vec.Vec.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
          payload {{«end»:=32#usize}} with
      | fail e => simp only [mapR,hp,bind_tc_fail]
      | div => simp only [mapR,hp,bind_tc_div]
      | ok chunk =>
        simp only [hp,bind_tc_ok]
        rw [←bytes chunk]
        cases hd : {S}.aspis_core.field.wide_exact.WideExact.from_le_bytes chunk with
        | fail e => simp only [mapR,hd,bind_tc_fail]
        | div => simp only [mapR,hd,bind_tc_div]
        | ok parsed =>
          cases parsed with
          | none => simp only [mapR,hd,bind_tc_ok,Option.map_none,errorMap,ProverCommitCircle25.fromError]
          | some x =>
            simp only [mapR,hd,bind_tc_ok,Option.map_some,
              {S}.aspis_core.field.wide_exact.WideExact.impl.c1,
              {C}.aspis_core.field.wide_exact.WideExact.impl.c1,zero_test]
            cases he : core.cmp.PartialEq.ne.trait_default
                {S}.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
                x.c1 {S}.aspis_core.field.QM31.ZERO with
            | fail e => simp only [he,bind_tc_fail]
            | div => simp only [he,bind_tc_div]
            | ok bad =>
              simp only [he,bind_tc_ok]
              cases bad with
              | true => simp only [if_true,errorMap,ProverCommitCircle25.fromError]
              | false =>
                simp only [Bool.false_eq_true,if_false,tailEq,bind_tc_ok,
                  ProverCommitFields20.clone_bytes,lift]
                exact tailRec

theorem fields (row : U8) (payload : alloc.vec.Vec U8) (value : Usize) :
    mapR errorMap ({S}.r1_wire.fields20.validate row payload value) =
      {C}.r1_wire.fields20.validate row payload value :=
  fields_bounded payload.val.length row payload value (by omega)

#print axioms fields_bounded
#print axioms fields
'''
s=s[:a]+extra+s[a:];p.write_text(s)
