"""Recover exact scratch-only harness text from the delivered patches."""
from pathlib import Path

def added_patch(path: Path, suffix: str) -> str:
    active=False
    lines=[]
    for line in path.read_text().splitlines(keepends=True):
        if line.startswith('+++ '):
            active=line.splitlines()[0][6:].endswith(suffix)
        elif active and line.startswith('+'):
            lines.append(line[1:])
    assert lines, (path,suffix)
    return ''.join(lines)

def pieces(e: Path) -> dict[str,bytes]:
    return {name:added_patch(e/file,suffix).encode() for name,file,suffix in [
        ('error','NBP_error.patch','/NBP_error.rs'),
        ('components','NBP_components.patch','/NBP_error.rs'),
        ('statement','NBP_statement.patch','/NBP_codecs.rs'),
        ('statement2','NBP_statement2.patch','/NBP_codecs.rs'),
        ('payments','NBP_payments.patch','/NBP_codecs.rs'),
        ('filled','NBP_filled.patch','/NBP_filled.rs'),
        ('forward','NBP_forward.patch','/NBP_error.rs')
    ]}
