#!/usr/bin/env python3
"""Offline PRE-EXEC policy specification. No exec/subprocess/build capability.

A real broker must stop EVERY execve/execveat before execution across all fork /
clone / vfork descendants, including shell/interpreter/native build-script
children, with identity-pinned executable/cwd/argv/env. Such a broker is NOT
implemented or authorized here. A rustc wrapper cannot supply that coverage.
"""
import dataclasses
COMPILER='/home/dombarker/.cache/solana/v1.52/platform-tools/rust/bin/rustc'
WRAPPER='/home/dombarker/project-offloads/codex-cx-sbf-recapture-20261024/rustc-diagnostics.py'
COMPILER_SHA='d95c95b68e321ad76634e1fd26b0a7c20ccdbae9ad9ca733f3ae2f2b4a0b6002'
WRAPPER_SHA='fa74d69e097b6eab43809943614133081abb6beb19406018961402b86494ff84'
@dataclasses.dataclass(frozen=True)
class Event:
    executable:str
    sha256:str
    argv:tuple
    phase:str
    complete_interception:bool=False
    identity_stable:bool=False

def decide(event):
    if not event.complete_interception or not event.identity_stable:
        return dict(allow=False,reason='No proven complete pre-exec interception/identity')
    # Exact version/sysroot queries only, preserving argv; no fake output.
    if event.executable==WRAPPER and event.sha256==WRAPPER_SHA and event.phase=='metadata':
        if event.argv in ((COMPILER,'-vV'),(COMPILER,'--print','sysroot')):
            return dict(allow=True,forward=event.argv,require_child=(COMPILER,COMPILER_SHA))
    if event.executable==COMPILER and event.sha256==COMPILER_SHA and event.phase=='metadata':
        if event.argv in (('-vV',),('--print','sysroot')):
            return dict(allow=True,forward=event.argv)
    # Concrete allowed source compile commands cannot yet be sealed: donor
    # provenance/registry/relocation/build-script inputs remain unresolved.
    # Deny build-script execution even for already-cached script binaries.
    return dict(allow=False,reason='No sealed concrete compile/build-script/child command authorization')
