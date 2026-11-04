from pathlib import Path
import sys
E=Path(__file__).resolve().parent
def d(i):return f"(a.next_frontier.val[{i}]'(by have := a.next_frontier.property; scalar_tac))"
for start in [16,12,8,4,0]:
 imp='NFR_AfterstateForwardHelpers' if start==16 else f'NFR_AfterstateForward{start+4:02}'
 s=f"""import {imp}
set_option autoImplicit false
noncomputable section
namespace NFR_AfterstateForward{start:02}
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
open AspisR1.S2K AspisS6NativeAfterstateDecoderFactored NFR_AfterstateForwardHelpers
theorem result (a : Afterstate)
    (valid : pool_v1.pair_terminal.validate_verified_afterstate a = ok (.Ok ())) :
    part_{start} (encoded a) a.next_root {' '.join(d(i) for i in range(start))} = ok (.Ok a) := by
  unfold part_{start}
"""
 for i in range(start,start+4):
  s+=f"""  rw [range (encoded a) {48+32*i}#usize {80+32*i}#usize (DigestBytes.bytes {d(i)})
    (by decide) (by simp [encoded,Array.to_slice,(AfterstateEncoding.bytes a).property])
    (frontier_window a {i} (by decide)),bind_tc_ok]
  rw [AspisR1.JFt_ExactArray.source _ _ _ rfl,bind_tc_ok]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rw [NFR_DigestForward.roundtrip _ ((domain a valid).2 ⟨{i},by decide⟩),bind_tc_ok]
  simp only [core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
"""
 if start==16:
  s+="""  rw [range (encoded a) 8#usize 16#usize (core.num.U64.to_le_bytes a.next_pair_index)
    (by decide) (by simp [encoded,Array.to_slice,(AfterstateEncoding.bytes a).property])
    (index_window a),bind_tc_ok]
  rw [AspisR1.JFt_ExactArray.source _ _ _ rfl,bind_tc_ok]
  simp only [lift,NFO_U64Roundtrip.from_to,bind_tc_ok,twenty_eta]
  have rebuilt : ({next_pair_index := a.next_pair_index, next_root := a.next_root, next_frontier := a.next_frontier} : Afterstate) = a := by cases a; rfl
  rw [rebuilt,valid]
  rfl
"""
 else:s+=f"  exact NFR_AfterstateForward{start+4:02}.result a valid\n"
 s+=f"#print axioms result\nend NFR_AfterstateForward{start:02}\n"
 out=E/f'NFR_AfterstateForward{start:02}.lean'
 if '--check' in sys.argv:
  assert out.read_text()==s, str(out)+' differs from generator'
 else:out.write_text(s)
print('Generated five bounded four-digest continuations')
