"""Disabled future fixed setup scope entry; no activation applied."""
def main():
    print('FinalNativeGate setup inside source-only: disabled')
    return 78

def _bound_body():
    import sys
    from pathlib import Path
    stage=Path('/home/dombarker/final-native-gate-v7-20261025')
    if Path(__file__).resolve().parent!=stage:raise ValueError('wrong fixed bootstrap path')
    sys.path.insert(0,str(stage))  # explicit fixed source bootstrap under -I
    from FinalNativeGate_scope import child_wait
    child_wait('setup')
    from FinalNativeGate_setup import _collect
    return _collect()


if __name__=='__main__':
    raise SystemExit(main())
