from pathlib import Path
for old,new in [('JFs_TX2_OuterActive','NBS_DotOuterActive'),('JFs_TX2_Outer','NBS_DotOuter')]:
 s=Path('lean/'+old+'.lean').read_text().replace('namespace AspisR1.'+old,'namespace '+new).replace('end AspisR1.'+old,'end '+new)
 s=s.replace('import JFs_TX2_OuterActive','import NBS_DotOuterActive')
 if old=='JFs_TX2_OuterActive':s='import NBS_DotInner\n'+s
 s=s.replace('open Aeneas Aeneas.Std Result ControlFlow','open Aeneas Aeneas.Std Result ControlFlow AspisR1')
 s=s.replace('(i : Fin 12) (slot : Fin 4)', '(q : Array U8 608#usize) (slot : Usize) (decoded : NBS_DotTerm.Scalars q slot)\n    (g : Array FIo_Install.NE 29#usize) (hg : FIo_ArrayCanon.Holds g)')
 s=s.replace('(JFr_TX2_Windows.array (JFn_Values.position i)) JFr_TX2_FirstLane.native\n        (Usize.ofNat slot.val (by have:=slot.isLt;scalar_tac))','q g slot')
 s=s.replace('(JFr_TX2_Windows.array (JFn_Values.position i)) JFr_TX2_FirstLane.native\n      (Usize.ofNat slot.val (by have:=slot.isLt;scalar_tac))','q g slot')
 s=s.replace('(JFr_TX2_Windows.array (JFn_Values.position i)) JFr_TX2_FirstLane.native\n          (Usize.ofNat slot.val (by have:=slot.isLt;scalar_tac))','q g slot')
 s=s.replace('JFs_TX2_Inner.source i slot', 'NBS_DotInner.source q slot decoded g hg')
 s=s.replace('JFs_TX2_OuterActive.source i slot','NBS_DotOuterActive.source q slot decoded g hg')
 Path('lean/'+new+'.lean').write_text(s)
