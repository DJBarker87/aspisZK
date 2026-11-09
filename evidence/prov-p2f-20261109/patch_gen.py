from pathlib import Path
import re
p=Path("PCUF_gen_equalities.py");t=p.read_text()
def rep(old,new,cnt=1):
    global t
    assert t.count(old)==cnt,(old[:60],t.count(old));t=t.replace(old,new)
# PCUC change 4
rep("""    new = ('@[' + ', '.join(kept) + ']\\n') if kept else ''
    rest = text[k:].lstrip('\\n')
    return text[:i] + new + rest""","""    # PCUF change 1 (= PCUC change 4): when `def` follows the attribute list on the SAME line, keep every column of that line
    eol = text.find('\\n', k); same_line = text[k:(eol if eol >= 0 else len(text))].strip() != ''
    if same_line:
        span = k - i; new1 = ('@[' + ', '.join(kept) + ']') if kept else ''
        assert len(new1) <= span
        return text[:i] + new1.ljust(span) + text[k:]
    new = ('@[' + ', '.join(kept) + ']\\n') if kept else ''
    rest = text[k:].lstrip('\\n')
    return text[:i] + new + rest""")
# PCUB change 3
rep("def generate(a):\n","""def rename_fresh(a, text):
    \"\"\"PCUF change 2 (= PCUB change 3): --rename-fresh OLD=NEW (repeatable). Rewrites the Lean path prefix OLD to NEW in the fresh text before it is parsed
    (word-boundary, path-prefix only); every rewrite is listed in the report.\"\"\"
    for pr in (getattr(a, 'rename_fresh', None) or []):
        old, new = pr.split('=', 1)
        text = re.sub(r'(?<![\\w.])' + re.escape(old) + r'(?=[\\w.])' if old.endswith('.') else r'(?<![\\w.])' + re.escape(old) + r'(?![\\w.])', new, text)
    return text

def generate(a):
""")
rep("fresh_text = fresh_path.read_text(); fh = header_info(fresh_text)","fresh_text = rename_fresh(a, fresh_path.read_text()); fh = header_info(fresh_text)")
rep("parse_blocks((Path(a.fresh_dir) / 'Types.lean').read_text())","parse_blocks(rename_fresh(a, (Path(a.fresh_dir) / 'Types.lean').read_text()))")
# PCUB change 4
rep("""                    if not hit: return True
""","""                    if not hit: return True
                    # PCUF change 3 (= PCUB change 4): a field type mentioning only alias types already classed rfl_candidate is copied field-by-field; Lean checks the defeq
                    if all(type_info.get(h, {}).get('cls') == 'rfl_candidate' for h in hit): return True
""")
rep("    ap.add_argument('--kind',","    ap.add_argument('--rename-fresh', action='append', help='PCUF change 2 (= PCUB change 3): OLD=NEW path-prefix rewrite of the fresh text'); ap.add_argument('--kind',")
p.write_text(t)
