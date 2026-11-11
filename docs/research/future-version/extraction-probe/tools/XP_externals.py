#!/usr/bin/env python3
"""Aspis extraction probe: for each emitted definition whose name starts with one of the given prefixes, list the
external axioms (FunsExternal template) that its own text and the text of its loop and closure helpers refer to.
usage: XP_externals.py <raw emission dir> <json-out> <prefix> [prefix...]"""
import re, sys, json
from pathlib import Path
raw = Path(sys.argv[1]); prefixes = sys.argv[3:]
ext = (raw / 'FunsExternal_Template.lean').read_text()
axioms = [a for a in re.findall(r'(?m)^axiom\s+(\S+)', ext)] + re.findall(r'(?m)^axiom\n\s+(\S+)', ext)
funs = (raw / 'Funs.lean').read_text()
parts = re.split(r'(?m)^(?=/-- )', funs); out = {}
def name(b):
    m = re.search(r'(?m)^(?:@\[[^\n]*\]\s*)?(?:noncomputable\s+)?(?:def|instance)\s*(\S*)', b)
    if not m: return None
    return m.group(1) or (re.search(r'(?m)^(?:def|instance)\s*\n\s*(\S+)', b) or [None, None])[1]
blocks = [(name(b), b) for b in parts if name(b)]
for p in prefixes:
    used = set(); n = 0; sorry = False
    for nm, b in blocks:
        if nm == p or nm.startswith(p + '_loop') or nm.startswith(p + '.closure') or nm.startswith(p + '.'):
            n += 1; body = re.sub(r'(?s)^/--.*?-/\n', '', b)
            sorry = sorry or bool(re.search(r'(?m)^\s*sorry\s*$', body))
            for a in axioms:
                if re.search(r'(?<![\w.])' + re.escape(a) + r'(?![\w])', body): used.add(a)
    out[p] = dict(declarations=n, placeholder_body=sorry, std_or_sdk_axioms=sorted(a for a in used if a.split('.')[0] in ('core', 'alloc', 'std', 'Slice', 'Shared0U64', 'solana_pubkey', 'solana_account_info', 'solana_instruction', 'solana_sha256_hasher', 'solana_hash', 'solana_msg', 'solana_program_error', 'solana_sdk_ids', 'MutAArray')),
                  aspis_axioms=sorted(a for a in used if a.split('.')[0] not in ('core', 'alloc', 'std', 'Slice', 'Shared0U64', 'solana_pubkey', 'solana_account_info', 'solana_instruction', 'solana_sha256_hasher', 'solana_hash', 'solana_msg', 'solana_program_error', 'solana_sdk_ids', 'MutAArray')))
json.dump(out, open(sys.argv[2], 'w'), indent=1)
for p, v in out.items(): print('%-52s decls %2d %s std=%s aspis=%s' % (p, v['declarations'], 'PLACEHOLDER' if v['placeholder_body'] else '', [a.replace('core.', 'c.')[-46:] for a in v['std_or_sdk_axioms']], [a[-34:] for a in v['aspis_axioms']]))
