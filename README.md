A simple hyperplonk prototype

```rust
use crate::{
    builder::{CircuitBuilder, Wire},
    commitment::MultilinearKzgScheme,
    function_sumcheck::Element,
    hyperplonk::{Gates, HyperPlonk},
};
use ark_bls12_381::{Bls12_381, Fr};
use ark_ff::UniformRand;
use rand::thread_rng;
use std::time::Instant;

const COLS: usize = 16;
type Plonk<G> = HyperPlonk<Fr, MultilinearKzgScheme<Bls12_381>, G, COLS, 2>;

//the gates of the proof system, this one in particular has two copies of some product gate
//there are no selectors implemented, so its easier to just have one gate
struct TestGate;
impl Gates<COLS, 2> for TestGate {
    fn function<F>(vars: &[F; COLS]) -> [F; 2]
    where
        F: Element<Out = F>,
        for<'a> &'a F: Element<Out = F>,
    {
        // let [a] = crate::gates::Sub::function(vars);
        let [b] = crate::gates::Product::function(vars);
        [b.clone(), b]
    }
}
const SIZE: usize = 1 << 16;
#[test]
fn proof_system() {
    //create a builder
    //builder just increases the count of rows and adds copy constraints
    let mut builder = CircuitBuilder::<COLS>::default();
    let mut rng = thread_rng();

    //add row, it should add selectors when the selector are implemented
    builder.add_row();
    for i in 1..SIZE {
        builder.add_row();
        //make elements in columns 4 and 5 the same
        builder.add_wire(Wire {
            cell1: (i - 1, 4),
            cell2: (i - 1, 5),
        });
        //make left input of product same as output of previous product
        builder.add_wire(Wire {
            cell1: (i - 1, 2),
            cell2: (i, 0),
        });
    }
    // builder.add_wire(Wire {
    // cell1: (0, 4),
    // cell2: (0, 5),
    // });
    let circuit: Plonk<TestGate> = builder.compile();

    let mut witness: Vec<[Fr; COLS]> = vec![];
    let mut last = Fr::rand(&mut rng);
    // let mut last = Fr::zero();
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
    // witness[5][4] = Fr::rand(&mut rng);

    let proof = circuit.prove(witness);

    let check = circuit.verify(proof);
    assert!(check);
}
```