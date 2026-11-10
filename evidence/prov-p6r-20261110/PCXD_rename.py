"""PCXD_rename.py: deterministic namespace rule PCXD-C2 (textual, per credited file).
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
# PCXD-C4 (added for the P3b V8R19 files, which each declare the helper namespaces PCVB_M31 / PCVB_QM / PCVB_R23): any token PCVB_<word> is suffixed _<tag>.
_old_rename = rename
def rename(text, tag, imports_wrapadd):
    t = _old_rename(text, tag, imports_wrapadd)
    return re.sub(r'(?<![\w.])(PCVB_[A-Za-z0-9]+)(?![\w])', lambda m: m.group(1) + '_' + tag, t)
