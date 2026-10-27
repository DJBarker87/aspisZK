from pathlib import Path
import json,re,sys
V=json.loads(Path('evidence/fixture-tx2g-20261026/JFw_POWERS.json').read_text())
def pack(a,s):return 'pack '+' '.join(str(x)+s for x in a)
def finish(prefix,d):
 slot=d['slot'];kind=d['kind'];k=d['k'];q=d['q'];v=V[k]
 s=prefix[:prefix.index('theorem source :')]
 s+=f'''theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P{k:02}.value
    JFr_TX2_Tails10.value{kind}_{slot}=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails10.value{kind}_{slot}=
      ok (.Ok ({pack(q,'#u32')})) := by
    apply JFs_TX2_CheckedQ.source
    change ({q[0]}<2147483647 ∧ {q[1]}<2147483647) ∧ ({q[2]}<2147483647 ∧ {q[3]}<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P{k:02}.value=
      ok (Array.make 2#usize [{pack(v[:4],'#u32')},{pack(v[4:],'#u32')}]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [{pack(v[:4],'#u32')},{pack(v[4:],'#u32')}])
      0#usize=ok ({pack(v[:4],'#u32')}) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [{pack(v[:4],'#u32')},{pack(v[4:],'#u32')}])
      1#usize=ok ({pack(v[4:],'#u32')}) := rfl
'''
 for half in range(2):
  s+=f'''  have d{half} : FIo_Native.fast_pairing.canonical.Dot.push before.c{half}
      ({pack(v[half*4:half*4+4],'#u32')}) ({pack(q,'#u32')})=ok after.c{half} := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair{half},bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {{start:=0#usize,«end»:=4#usize}}
      ⟨{pack(d['before'][half*4:half*4+4],'#u64')}⟩ raw{half}=_
    simp only [raw{half},JFw_TX2_FoldPush.source]
    rfl
'''
 s+=f'''  simp only [FIo_Native.fast_pairing.EbyKDot.push,if_neg full,hw,r0,r1,checked,
    bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,lift,d0,d1]
  have inc : Usize.wrapping_add before.count 1#usize=after.count := by
    apply UScalar.eq_of_val_eq
    exact Port3_Wrapping.increment before.count (by unfold before;decide)
  rw [inc]
#print axioms pair0
#print axioms pair1
#print axioms source
end AspisR1.JFw_TX2_Raw{slot}{kind}
end
'''
 return s

if __name__=="__main__":
 D=json.loads(Path("evidence/fixture-tx2g-20261026/JFw_RAW.json").read_text())
 for d in D:
  p=Path(f"lean/JFw_TX2_Raw{d['slot']}{d['kind']}.lean")
  s=finish(p.read_text(),d)
  if "--check" in sys.argv:assert p.read_text()==s,str(p)
  else:p.write_text(s)
