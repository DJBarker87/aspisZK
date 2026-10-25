#!/usr/bin/env python3
"""Source-only ledger citation check. Never invokes Lean or any build tool.

This intentionally recognizes explicit, line-oriented Lean declarations and
structure fields, not elaborator-generated declarations, macros or imports.
Unsupported spelling fails closed as a missing citation. It is not a Lean parser
or a proof/axiom/closure checker. Reads current source and requires cited files to equal their HEAD blobs.
The ledger itself may be edited, so proposed documentation can be checked before
committing. Unrelated working-tree changes do not affect this check.
"""
from __future__ import annotations

import argparse
from pathlib import Path
import re
import subprocess
import sys
from urllib.parse import unquote

NAME = r"[\w'.]+"
LINK = re.compile(r"\[([^\]\n]+)\]\(([^)\s]+)\)")
DECL = re.compile(r"^(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*(?:theorem|lemma|def|abbrev|opaque|axiom|structure|class|inductive)\s+(" + NAME + r")\b")


def scrub(source: str) -> str:
    """Blank nested comments and string literals while preserving line positions."""
    result = list(source)
    i, depth, string = 0, 0, False
    while i < len(source):
        if depth:
            if source.startswith('/-', i):
                result[i:i+2] = '  '
                depth += 1
                i += 2
                continue
            if source.startswith('-/', i):
                result[i:i+2] = '  '
                depth -= 1
                i += 2
                continue
        elif string:
            if source[i] == '\\':
                result[i] = ' '
                i += 1
                if i < len(source) and source[i] != '\n':
                    result[i] = ' '
                i += 1
                continue
            if source[i] == '"':
                string = False
        elif source.startswith('/-', i):
            depth = 1
            result[i:i+2] = '  '
            i += 2
            continue
        elif source.startswith('--', i):
            end = source.find('\n', i)
            if end < 0:
                end = len(source)
            result[i:end] = ' ' * (end-i)
            i = end
            continue
        elif source[i] == '"':
            string = True
        else:
            i += 1
            continue
        if source[i] != '\n':
            result[i] = ' '
        i += 1
    if depth or string:
        raise ValueError('unterminated comment or string')
    return ''.join(result)


def declarations(source: str) -> set[str]:
    scopes: list[tuple[str, str]] = []
    found: set[str] = set()
    structure = None
    header = False
    def qualified(name: str) -> str:
        if name.startswith('_root_.'):
            return name[7:]
        prefix = '.'.join(n for kind, n in scopes if kind == 'namespace')
        return f'{prefix}.{name}' if prefix else name
    for line in scrub(source).splitlines():
        stripped = line.strip()
        if not stripped:
            continue
        ns = re.fullmatch(r'namespace\s+(' + NAME + ')', stripped)
        section = re.fullmatch(r'(?:noncomputable\s+)?section(?:\s+(' + NAME + '))?', stripped)
        end = re.fullmatch(r'end(?:\s+(' + NAME + '))?', stripped)
        if ns or section or end:
            structure = None
            if ns:
                scopes.append(('namespace', ns.group(1)))
            elif section:
                scopes.append(('section', section.group(1) or ''))
            elif scopes:
                kind, name = scopes.pop()
                if end.group(1) and end.group(1) != name:
                    raise ValueError(f'unsupported scope end: {stripped}')
            continue
        # Strip command attributes without treating their contents as names.
        command = re.sub(r'^\s*@\[[^]]*\]\s*', '', line).lstrip()
        decl = DECL.match(command)
        if decl and not line.startswith('  '):
            name = qualified(decl.group(1))
            found.add(name)
            structure = name if re.match(r'^(structure|class)\s', command) else None
            header = bool(structure and 'where' not in command)
            continue
        if structure:
            if header:
                if re.search(r'\bwhere\s*$', stripped):
                    header = False
                continue
            field = re.match(r'^  ([\w\']+)\s*:', line)
            if field:
                found.add(structure + '.' + field.group(1))
            elif not line[0].isspace():
                structure = None
    return found


def check(root: Path, ledger: Path) -> tuple[int, int]:
    citations = []
    errors = []
    cache = {}
    content = ledger.read_text(encoding='utf-8')
    for match in LINK.finditer(content):
        label, target = match.groups()
        if '.lean' not in target:
            continue
        line = content.count('\n', 0, match.start()) + 1
        if '#decl=' not in target:
            errors.append(f'{line}: Lean link requires #decl=qualified.name: {target}')
            continue
        file, name = target.split('#decl=', 1)
        file, name = unquote(file), unquote(name)
        path = (ledger.parent / file).resolve()
        citations.append((path, name))
        try:
            relative = path.relative_to(root)
            if path.suffix != '.lean' or not name or label.strip('`') != name:
                raise ValueError('invalid suffix, empty declaration, or label/name mismatch')
            if path not in cache:
                committed = subprocess.run(
                    ['git', '-C', str(root), 'show', f'HEAD:{relative.as_posix()}'],
                    capture_output=True,
                )
                if committed.returncode:
                    raise ValueError('source file does not exist at HEAD')
                current = path.read_bytes()
                if current != committed.stdout:
                    raise ValueError('cited source differs from HEAD; commit or restore it first')
                cache[path] = declarations(current.decode('utf-8'))
            if name not in cache[path]:
                raise ValueError(f'declaration not found in {relative}: {name}')
        except (ValueError, OSError) as error:
            errors.append(f'{line}: {error}')
    if not citations:
        errors.append('no Lean citations found')
    for error in errors:
        print('ERROR: ' + error, file=sys.stderr)
    return len(citations), len(errors)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--ledger', type=Path, help='alternate ledger for negative checks')
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[2]
    ledger = (args.ledger or root / 'design/RELEASE-LEDGER-20261025.md').resolve()
    count, errors = check(root, ledger)
    revision = subprocess.check_output(['git', '-C', str(root), 'rev-parse', 'HEAD'], text=True).strip()
    print(f'{"FAIL" if errors else "PASS"}: {count} Lean citations; {errors} errors; HEAD {revision}; source matches HEAD; declaration existence only')
    return bool(errors)


if __name__ == '__main__':
    sys.exit(main())
