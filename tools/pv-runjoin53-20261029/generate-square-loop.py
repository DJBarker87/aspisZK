from pathlib import Path
import importlib.util
T=Path(__file__).parent;sp=importlib.util.spec_from_file_location('w',T/'write-module.py');w=importlib.util.module_from_spec(sp);sp.loader.exec_module(w)
body='open PV_RunJoin_CircleNeutralFinite53 PV_RunJoin_CircleNeutralRange53\n'
for name,raw,finite in [('owned','PV_RunJoin_CircleRawScalar52','finite'),('model','PV_RunJoin_CircleR72Raw52','PV_RunJoin_CircleNeutralFinite53.model')]:
 body+=f'''
theorem {name} (n : Nat) (r : core.ops.range.Range Usize) (a : U32)
    (hr : r.end.val=r.start.val+n) :
    {raw}.field.square_n_loop r a = {finite} n a := by
  induction n generalizing r a with
  | zero =>
    have hn := next_none r (by omega)
    rw [PV_RunJoin_CircleNeutralSquareEquation53.{name}]
    simp only [{raw}.field.square_n_loop.body,hn,bind_tc_ok,{finite}]
    rfl
  | succ n ih =>
    obtain ⟨after,hn,hs,he⟩ := next_some r (by omega)
    have hafter : after.end.val=after.start.val+n := by rw [he];omega
    rw [PV_RunJoin_CircleNeutralSquareEquation53.{name}]
    rw [PV_RunJoin_CircleNeutralSquareCell53.{name} r after a hn]
    simp only [bind_assoc_eq,bind_tc_ok]
    change (do let v ← {raw}.field.M31.mul a a
               {raw}.field.square_n_loop after v) = {finite} (n+1) a
    rw [{finite}]
    apply congrArg (Aeneas.Std.bind ({raw}.field.M31.mul a a))
    funext v
    exact ih after v hafter
'''
w.write('PV_RunJoin_CircleNeutralSquareLoop53',['R1Z.PV_RunJoin_CircleNeutralRange53','R1Z.PV_RunJoin_CircleNeutralFinite53','R1Z.ProverRw19LoopBind','R1Z.PV_RunJoin_CircleNeutralSquareEquation53','R1Z.PV_RunJoin_CircleNeutralSquareCell53'],body,['owned','model'])
w.write('PV_RunJoin_CircleNeutralSquareN53',['R1Z.PV_RunJoin_CircleNeutralSquareLoop53'],'''open PV_RunJoin_CircleNeutralShape53

theorem complete (a : U32) (ha : Canon a) (count : Usize) :
    ∃ y, PV_RunJoin_CircleRawScalar52.field.square_n a count = ok y ∧
      PV_RunJoin_CircleR72Raw52.field.square_n a count = ok y ∧ Canon y := by
  obtain ⟨y,hy,hy',hc⟩ := PV_RunJoin_CircleNeutralFinite53.total count.val a ha
  refine ⟨y,?_,?_,hc⟩
  · unfold PV_RunJoin_CircleRawScalar52.field.square_n
    rw [PV_RunJoin_CircleNeutralSquareLoop53.owned count.val _ a (by simp)]
    exact hy
  · unfold PV_RunJoin_CircleR72Raw52.field.square_n
    rw [PV_RunJoin_CircleNeutralSquareLoop53.model count.val _ a (by simp)]
    exact hy'
''',['complete'])
