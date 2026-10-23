fn box_from_parts(variant:Variant,factors:[[[K;4];5];5],points:[[K;10];3],extra:[K;2])->Box<Self> {
        Box::new(Self { variant, factors, points, extra })
    }
