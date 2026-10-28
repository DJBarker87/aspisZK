from pathlib import Path
p=Path('lean/NCB_TailOffsets.lean');s=p.read_text();pos=s.index('#print axioms first')
s=s[:pos]
for k in [1,2]:
 off=16*(k-1)
 s+=f'''
theorem {'second' if k==1 else 'third'} (q : Array U8 608#usize) (s : Fin 4) :
    FJi_TailInputs.read{k} q (slot s)=JFr_TX2_TailRead.read q
      (JFr_TX2_Tails.offset s {k}) (JFr_TX2_Tails.stop s {k}) := by
  let delta : Usize := Usize.ofNat (s.val*32) (by have:=s.isLt;scalar_tac)
  let base : Usize := Usize.ofNat (480+s.val*32) (by have:=s.isLt;scalar_tac)
  have mul : slot s*32#usize=ok delta :=
    Port4A_ReaderInstall.mul_value _ _ (by change s.val*32≤65536;have:=s.isLt;omega)
  have add : 480#usize+delta=ok base :=
    Port4A_ReaderInstall.add_value _ _ (by change 480+s.val*32≤65536;have:=s.isLt;omega)
  have small : ({k-1}#usize*16#usize : Result Usize)=ok {off}#usize := by decide
  have start : base+{off}#usize=ok (JFr_TX2_Tails.offset s {k}) := by
    have h := Port4A_ReaderInstall.add_value base {off}#usize (by change 480+s.val*32+{off}≤65536;have:=s.isLt;omega)
    exact h.trans (congrArg Result.ok (by
      apply UScalar.eq_of_val_eq
      change 480+s.val*32+{off}=JFr_TX2_Tails.start s {k}
      simp [JFr_TX2_Tails.start,Nat.mul_comm]))
  have stop : JFr_TX2_Tails.offset s {k}+16#usize=ok (JFr_TX2_Tails.stop s {k}) := by
    apply Port4A_ReaderInstall.add_value
    change JFr_TX2_Tails.start s {k}+16≤65536
    simp only [JFr_TX2_Tails.start]
    have:=s.isLt
    omega
  simp only [FJi_TailInputs.read{k},mul,add,small,start,stop,bind_tc_ok,JFr_TX2_TailRead.read]
'''
s+='\n#print axioms first\n#print axioms second\n#print axioms third\nend NCB_TailOffsets\nend\n';p.write_text(s)
