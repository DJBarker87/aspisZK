from pathlib import Path
s=Path('lean/JFs_TX2_Inner.lean').read_text().replace('import JFs_TX2_Term','import NBS_DotTerm').replace('AspisR1.JFs_TX2_Inner','NBS_DotInner')
s=s.replace('(i : Fin 12) (slot : Fin 4)', '(q : Array U8 608#usize) (slot : Usize) (decoded : NBS_DotTerm.Scalars q slot)\n    (g : Array AspisR1.FIo_Install.NE 29#usize) (hg : AspisR1.FIo_ArrayCanon.Holds g)')
s=s.replace('open Aeneas Aeneas.Std Result ControlFlow','open Aeneas Aeneas.Std Result ControlFlow AspisR1')
s=s.replace('(JFr_TX2_Windows.array (JFn_Values.position i)) JFr_TX2_FirstLane.native\n      (Usize.ofNat slot.val (by have:=slot.isLt;scalar_tac))','q g slot')
s=s.replace('(JFr_TX2_Windows.array (JFn_Values.position i)) JFr_TX2_FirstLane.native\n        (Usize.ofNat slot.val (by have:=slot.isLt;scalar_tac))','q g slot')
s=s.replace('JFs_TX2_Term.source i slot r s','NBS_DotTerm.source q slot decoded g hg r s')
Path('lean/NBS_DotInner.lean').write_text(s)
