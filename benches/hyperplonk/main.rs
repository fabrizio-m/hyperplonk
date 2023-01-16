use criterion::{criterion_group, criterion_main, Criterion};

pub fn criterion_benchmark(c: &mut Criterion) {
    //c.bench_function("fib 20", |b| b.iter(|| fibonacci(black_box(20))));
    let circuit = test::circuit();
    let witness = test::witness();
    c.bench_function("hyperplonk 2^16", |b| {
        b.iter_with_large_drop(|| {
            let proof = circuit.prove(witness.clone());
            proof
        });
    });
}
mod test {
    use ark_bls12_381::{Bls12_381, Fr};
    use ark_ff::UniformRand;
    use hyperplonk::{
        builder::{CircuitBuilder, Wire},
        commitment::MultilinearKzgScheme,
        hyperplonk::{Gates, HyperPlonk},
        Element,
    };
    use rand::thread_rng;

    const COLS: usize = 16;
    type Plonk<G> = HyperPlonk<Fr, MultilinearKzgScheme<Bls12_381>, G, COLS, 2>;

    pub struct TestGate;
    impl Gates<COLS, 2> for TestGate {
        fn function<F>(vars: &[F; COLS]) -> [F; 2]
        where
            F: Element<Out = F>,
            for<'a> &'a F: Element<Out = F>,
        {
            let [_a] = hyperplonk::gates::Sub::function(vars);
            let [b] = hyperplonk::gates::Product::function(vars);
            [b.clone(), b]
        }
    }

    const SIZE: usize = 1 << COLS;
    pub fn circuit() -> Plonk<TestGate> {
        let mut builder = CircuitBuilder::<COLS>::default();

        builder.add_row();
        for i in 1..SIZE {
            builder.add_row();
            builder.add_wire(Wire {
                cell1: (i - 1, 4),
                cell2: (i - 1, 5),
            });
            builder.add_wire(Wire {
                cell1: (i - 1, 2),
                cell2: (i, 0),
            });
        }
        let circuit: Plonk<TestGate> = builder.compile();
        circuit
    }
    pub fn witness() -> Vec<[Fr; COLS]> {
        let mut rng = thread_rng();
        let mut witness: Vec<[Fr; COLS]> = vec![];
        let mut last = Fr::rand(&mut rng);
        for _ in 0..SIZE {
            let mut row = [(); COLS].map(|_| Fr::rand(&mut rng));
            let new = Fr::rand(&mut rng);
            row[0] = last;
            row[1] = new;
            row[2] = last * new;
            last = row[2];
            row[4] = new;
            row[5] = new;
            witness.push(row);
        }
        // let proof = circuit.prove(witness);
        // let check = circuit.verify(proof);
        // assert!(check);
        witness
    }
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
