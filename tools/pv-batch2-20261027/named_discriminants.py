"""Final generation adaptation for private PV carriers, idempotent and checked."""
def qualify(source: str) -> str:
    if '@[discriminant ' not in source and '@[pv_b2_discriminant ' not in source:
        return source
    source=source.replace('@[discriminant ','@[pv_b2_discriminant ')
    header='import R1Z.PV_B2_D_NamedDiscriminant\n'
    if header not in source:
        pos=source.index('import ')
        source=source[:pos]+header+source[pos:]
    return source
