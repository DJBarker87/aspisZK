fn semantic_boundary(polynomial: &[QM31; 28]) -> QM31 {
        let boundary = polynomial.iter().copied().fold(polynomial[0], QM31::add);
    boundary
}
