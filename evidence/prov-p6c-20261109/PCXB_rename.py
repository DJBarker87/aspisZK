"""PCXB_rename.py: deterministic namespace rule PCXB-C2 (textual, per credited file).
tag = Ckk_Fjj (bundle kk, file index jj).  Within the file text (import lines removed):
  PRVEq.        -> PRVEq.<tag>.        (theorem namespace; only a word-start `PRVEq.` token)
  PRVFresh_     -> PRVFresh_<tag>_     (fresh-emission namespaces)
  helper namespaces H in {PRVH, PRVC, PCVE, PCVEhelpers}: token H followed by `.` or end-of-name, and `namespace H` -> H_<tag>
    (not applied to references to the imported module PRVH_WrapAdd: for a file that imports PRVH_WrapAdd, PRVH is left unrenamed)
Gate namespaces and gate constants are never touched."""
import re
HELP = ['PRVH', 'PRVC', 'PCVEhelpers', 'PCVE']
def rename(text, tag, imports_wrapadd):
    t = re.sub(r'(?<![\w.])PRVEq\.', f'PRVEq.{tag}.', text)
    t = re.sub(r'(?<![\w])PRVFresh_', f'PRVFresh_{tag}_', t)
    for h in HELP:
        if h == 'PRVH' and imports_wrapadd: continue
        t = re.sub(r'(?<![\w.])' + h + r'(?![\w])', f'{h}_{tag}', t)
    return t
