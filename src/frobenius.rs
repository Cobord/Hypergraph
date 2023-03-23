#[allow(dead_code)]
enum FrobeniusOperation<Lambda: Eq + Copy, BlackBoxLabel> {
    Unit(Lambda),
    Multiplication(Lambda),
    Comultiplication(Lambda),
    Counit(Lambda),
    Identity(Lambda),
    SymmetricBraiding(Lambda, Lambda),
    UnSpecifiedBox(BlackBoxLabel, Vec<Lambda>, Vec<Lambda>),
}

impl<'a, Lambda, BlackBoxLabel> FrobeniusOperation<Lambda, BlackBoxLabel>
where
    Lambda: Eq + Copy,
{
    fn source_size(&self) -> usize {
        match self {
            Self::Unit(_) => 0,
            Self::Multiplication(_) => 2,
            Self::Comultiplication(_) => 1,
            Self::Counit(_) => 1,
            Self::Identity(_) => 1,
            Self::SymmetricBraiding(_, _) => 2,
            Self::UnSpecifiedBox(_, srcs, _) => srcs.len(),
        }
    }

    fn target_size(&self) -> usize {
        match self {
            Self::Unit(_) => 1,
            Self::Multiplication(_) => 1,
            Self::Comultiplication(_) => 2,
            Self::Counit(_) => 0,
            Self::Identity(_) => 1,
            Self::SymmetricBraiding(_, _) => 2,
            Self::UnSpecifiedBox(_, _, tgts) => tgts.len(),
        }
    }

    fn source_types(&self) -> Vec<Lambda> {
        match self {
            Self::Unit(_) => vec![],
            Self::Multiplication(z) => vec![*z, *z],
            Self::Comultiplication(z) => vec![*z],
            Self::Counit(z) => vec![*z],
            Self::Identity(z) => vec![*z],
            Self::SymmetricBraiding(z, w) => vec![*z, *w],
            Self::UnSpecifiedBox(_, srcs, _) => srcs.clone(),
        }
    }

    fn target_types(&self) -> Vec<Lambda> {
        match self {
            Self::Unit(z) => vec![*z],
            Self::Multiplication(z) => vec![*z],
            Self::Comultiplication(z) => vec![*z, *z],
            Self::Counit(_) => vec![],
            Self::Identity(z) => vec![*z],
            Self::SymmetricBraiding(z, w) => vec![*w, *z],
            Self::UnSpecifiedBox(_, _, tgts) => tgts.clone(),
        }
    }
}

#[allow(dead_code)]
struct FrobeniusBlock<Lambda: Eq + Copy, BlackBoxLabel> {
    op: FrobeniusOperation<Lambda, BlackBoxLabel>,
    source_side_placement: usize,
    target_side_placement: usize,
}

impl<'a, Lambda, BlackBoxLabel> FrobeniusBlock<Lambda, BlackBoxLabel>
where
    Lambda: Eq + Copy,
{
    fn new(
        op: FrobeniusOperation<Lambda, BlackBoxLabel>,
        source_side_placement: usize,
        target_side_placement: usize,
    ) -> Self {
        Self {
            op,
            source_side_placement,
            target_side_placement,
        }
    }

    fn source_size(&self) -> usize {
        self.op.source_size()
    }

    #[allow(dead_code)]
    fn source_idces(&self) -> Vec<usize> {
        let my_source_size = self.source_size();
        (0..my_source_size)
            .map(|z| z + self.source_side_placement)
            .collect()
    }

    fn target_size(&self) -> usize {
        self.op.target_size()
    }

    #[allow(dead_code)]
    fn target_idces(&self) -> Vec<usize> {
        let my_target_size = self.target_size();
        (0..my_target_size)
            .map(|z| z + self.target_side_placement)
            .collect()
    }
}

#[allow(dead_code)]
struct FrobeniusLayer<Lambda: Eq + Copy, BlackBoxLabel> {
    blocks: Vec<FrobeniusBlock<Lambda, BlackBoxLabel>>,
    left_type: Vec<Lambda>,
    right_type: Vec<Lambda>,
}

impl<'a, Lambda, BlackBoxLabel> FrobeniusLayer<Lambda, BlackBoxLabel>
where
    Lambda: Eq + Copy,
{
    #[allow(dead_code)]
    pub fn new() -> Self {
        Self {
            blocks: vec![],
            left_type: vec![],
            right_type: vec![],
        }
    }

    #[allow(dead_code)]
    pub fn append_block(&mut self, op: FrobeniusOperation<Lambda, BlackBoxLabel>) {
        let source_side_placement = self.left_type.len();
        let target_side_placement = self.right_type.len();
        self.left_type.extend(op.source_types());
        self.right_type.extend(op.target_types());
        let my_op = FrobeniusBlock::<Lambda, BlackBoxLabel>::new(
            op,
            source_side_placement,
            target_side_placement,
        );
        self.blocks.push(my_op);
    }

    #[allow(dead_code)]
    pub fn monoidal(&mut self, other: Self) {
        for new_op in other.blocks {
            self.append_block(new_op.op);
        }
    }
}
