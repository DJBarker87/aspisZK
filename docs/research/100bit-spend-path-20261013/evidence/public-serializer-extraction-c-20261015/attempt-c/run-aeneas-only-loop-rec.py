#!/usr/bin/env python3
"""Translate the already-pinned attempt-b LLBC only; does not run Cargo/Charon."""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys

AENEAS = Path('/home/dombarker/project-offloads/aspis-v7-aeneas-source-unblock-20260830/aeneas-repro-r1')
AENEAS_SHA256 = 'e3e6e658ad26168421eb37627561930c1e13afa978f77b214a1201d9c4faa813'
LLBC_SHA256 = '4bc765cb58336cee6c3c5a702e14622c285aabf267656ccb6e0e7665169f307c'
NAMESPACE = 'AspisR1PublicSerializer'


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_json(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')


def public_bytes_rows(llbc: dict) -> list[dict]:
    translated = llbc.get('translated', {})
    rows = []
    for row in translated.get('fun_decls', []):
        if not isinstance(row, dict):
            continue
        meta = row.get('item_meta', {})
        names = meta.get('name', [])
        terminal = names[-1] if names else None
        if (isinstance(terminal, dict)
                and terminal.get('Ident') == ['public_bytes', 0]
                and meta.get('is_local') is True
                and isinstance(meta.get('source_text'), str)
                and meta['source_text'].startswith('pub fn public_bytes(')
                and isinstance(row.get('body'), dict)
                and isinstance(row['body'].get('Structured'), dict)):
            rows.append(row)
    return rows


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument('--llbc', type=Path, required=True)
    ap.add_argument('--output', type=Path)
    ap.add_argument('--preflight-only', action='store_true',
                    help='validate pinned LLBC manifest locally without invoking Aeneas')
    args = ap.parse_args()
    if not args.llbc.is_file() or sha(args.llbc) != LLBC_SHA256:
        raise SystemExit('saved attempt-b LLBC pin mismatch')
    llbc = json.loads(args.llbc.read_text())
    translated = llbc.get('translated', {})
    if not translated.get('ordered_decls'):
        raise SystemExit('refusing LLBC with empty ordered_decls')
    target_rows = public_bytes_rows(llbc)
    if len(target_rows) != 1:
        raise SystemExit(f'refusing LLBC without exactly one local public_bytes structured body; found {len(target_rows)}')
    if args.preflight_only:
        print(json.dumps({'status': 'preflight_ok', 'llbc_sha256': LLBC_SHA256,
                          'ordered_decl_count': len(translated['ordered_decls']),
                          'public_bytes_body_count': len(target_rows),
                          'span': target_rows[0]['body']['Structured']['span']}))
        return 0
    if args.output is None:
        raise SystemExit('--output is required unless --preflight-only is selected')
    if not AENEAS.is_file() or sha(AENEAS) != AENEAS_SHA256:
        raise SystemExit('Aeneas binary pin mismatch')
    if args.output.exists():
        raise SystemExit('output must be a fresh directory; preserve prior attempts')
    args.output.mkdir(parents=True)
    shutil.copy2(args.llbc, args.output / 'PublicSerializer.llbc')
    runner = Path(__file__).resolve()
    shutil.copy2(runner, args.output / runner.name)
    write_json(args.output / 'pins.json', {
        'aeneas_path': str(AENEAS), 'aeneas_sha256': AENEAS_SHA256,
        'llbc_sha256': LLBC_SHA256,
        'runner_path': str(runner), 'runner_sha256': sha(runner),
        'translation_mode': 'Aeneas-only on attempt-b LLBC; -loops-to-rec',
        'source_revision': 'e4a5808dd061cf373b27d130f7d66eb8f0214db9',
    })
    command = [str(AENEAS), '-sequential', '-no-progress-bar', '-abort-on-error',
               '-loops-to-rec', '-backend', 'lean', '-namespace', NAMESPACE,
               '-dest', str(args.output / 'generated'), '-subdir', NAMESPACE,
               '-split-files', '-emit-json', str(args.output / 'PublicSerializer.llbc')]
    write_json(args.output / 'commands.json', [{'label': 'translate-loop-rec', 'command': command}])
    with (args.output / 'aeneas.log').open('w') as log:
        proc = subprocess.run(['/usr/bin/time', '-v', '-o', str(args.output / 'aeneas.time.log'),
                               *command], stdout=log, stderr=subprocess.STDOUT)
    result = {'exit': proc.returncode, 'status': 'translation_failed' if proc.returncode else 'translation_completed',
              'target': 'local public_bytes serializer method', 'llbc_sha256': LLBC_SHA256}
    rejected = None
    if proc.returncode == 0:
        manifest = args.output / 'generated' / 'translation.json'
        if not manifest.is_file():
            result.update({'status': 'rejected_empty_translation', 'reason': 'missing translation.json'})
            rejected = 'Aeneas returned success without translation.json'
        else:
            translation = json.loads(manifest.read_text())
            functions = translation.get('functions', [])
            types = translation.get('types', [])
            targets = [f for f in functions if f.get('is_local') is True
                       and f.get('rust_name', '').endswith('::public_bytes')]
            result.update({'function_count': len(functions), 'type_count': len(types),
                           'target_function_count': len(targets), 'target_functions': targets})
            if not functions or not types or len(targets) != 1:
                result['status'] = 'rejected_empty_or_missing_target'
                rejected = 'rejecting empty/missing-target Aeneas output'
            else:
                target = targets[0]
                lean = args.output / 'generated' / target['lean_file']
                if not lean.is_file() or target['lean_name'].rsplit('.', 1)[-1] not in lean.read_text():
                    result['status'] = 'rejected_missing_lean_target'
                    rejected = 'translation manifest target has no Lean declaration'
    write_json(args.output / 'aeneas-result.json', result)
    pinned = {str(p.relative_to(args.output)): sha(p)
              for base in [args.output / 'generated'] if base.exists()
              for p in base.rglob('*') if p.is_file()}
    for name in ['PublicSerializer.llbc', runner.name, 'commands.json', 'pins.json', 'aeneas.log',
                 'aeneas.time.log', 'aeneas-result.json']:
        p = args.output / name
        if p.is_file():
            pinned[name] = sha(p)
    write_json(args.output / 'artifact-pins.json', pinned)
    if proc.returncode:
        raise SystemExit(proc.returncode)
    if rejected:
        raise SystemExit(rejected)
    print(json.dumps({'status': result['status'], 'target_count': result['target_function_count']}))
    return 0

if __name__ == '__main__':
    raise SystemExit(main())
