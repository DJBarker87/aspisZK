#!/usr/bin/env python3
"""X1b: a minimal call-graph reader for the LLBC of Charon 454586e9 (spans under `Untagged`/`Deduplicated`, hash-consed
values). The privacy lead's c2_graph.py stops on this format (KeyError 'data' at item_meta.span), so its edge rule is
re-implemented here: f -> g when the body of f holds `Fun: {Regular: g}` outside a `Drop` statement; trait-method calls
through a named impl add every method of that impl."""
import json
def nm(name):
    out = []
    for e in name:
        if 'Ident' in e: out.append(e['Ident'][0])
        elif 'Impl' in e: out.append('{impl}')
        elif 'Monomorphized' in e: pass
        else: out.append('{%s}' % next(iter(e)))
    return '::'.join(out)
class LLBC:
    def __init__(self, path):
        d = json.load(open(path)); tr = d['translated']; self.tr = tr; self.HC = {}
        stack = [d]
        while stack:
            x = stack.pop()
            if isinstance(x, dict):
                for k, v in x.items():
                    if k in ('HashConsedValue', 'Value') and isinstance(v, list) and len(v) == 2 and isinstance(v[0], int): self.HC[v[0]] = v[1]
                    stack.append(v)
            elif isinstance(x, list): stack.extend(x)
        self.fun = {f['def_id']: f for f in tr['fun_decls'] if f}
        self.impls = {t['def_id']: t for t in tr['trait_impls'] if t}
        self.files = {f['id']: (f['name'].get('Local') or f['name'].get('Virtual') or json.dumps(f['name'])) for f in tr['files'] if f}
        self.name = {i: nm(f['item_meta']['name']) for i, f in self.fun.items()}
        self.memo = {}; self.direct = {}
        for i, f in self.fun.items():
            if isinstance(f.get('body'), dict) and ('Structured' in f['body'] or 'Unstructured' in f['body']):
                self.direct[i] = self.walk(f['body'])[0]
    def span(self, i):
        s = self.fun[i]['item_meta']['span']
        s = s.get('Untagged', s)
        if 'Deduplicated' in s: s = self.HC.get(s['Deduplicated'], s)
        if 'Value' in s: s = s['Value'][1]
        s = s.get('data', s)
        return self.files.get(s.get('file_id'), '?'), s.get('beg', {}).get('line')
    def walk(self, x):
        funs = set(); impls = set(); stack = [x]; seen = set()
        while stack:
            v = stack.pop()
            if isinstance(v, list): stack.extend(v); continue
            if not isinstance(v, dict): continue
            for k, w in v.items():
                if k == 'Drop': continue
                if k == 'Deduplicated' and isinstance(w, int):
                    if w not in seen:
                        seen.add(w)
                        if w not in self.memo:
                            self.memo[w] = (set(), set()); self.memo[w] = self.walk(self.HC.get(w))
                        funs |= self.memo[w][0]; impls |= self.memo[w][1]
                    continue
                if k == 'Fun' and isinstance(w, dict) and isinstance(w.get('Regular'), int): funs.add(w['Regular'])
                if k == 'Regular' and isinstance(w, dict) and isinstance(w.get('kind'), dict) and isinstance(w['kind'].get('Fun'), int): funs.add(w['kind']['Fun'])
                if k == 'TraitImpl' and isinstance(w, dict) and isinstance(w.get('id'), int): impls.add(w['id'])
                stack.append(w)
        return funs, impls
