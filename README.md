# Lambdaworks Plonk Prover
Fast implementation of the Plonk zk protocol written in Rust. This is part of the [Lambdaworks](https://github.com/lambdaclass/lambdaworks) framework. It comes with a high-level API to build your own circuits.

<div>

[![Telegram Chat][tg-badge]][tg-url]
[![codecov](https://img.shields.io/codecov/c/github/lambdaclass/lambdaworks)](https://codecov.io/gh/lambdaclass/lambdaworks)

[tg-badge]: https://img.shields.io/static/v1?color=green&logo=telegram&label=chat&style=flat&message=join
[tg-url]: https://t.me/+98Whlzql7Hs0MDZh

</div>

## Building a circuit
The following code creates a circuit representing the program that has two public inputs `x` and `y` and asserts `x*e=y`:

```rust
let system = &mut ConstraintSystem::<FrField>::new();
let x = system.new_public_input();
let y = system.new_public_input();
let e = system.new_variable();

let z = system.mul(&x, &e);    
system.assert_eq(&y, &z);;
```

## Setup
The setup generates a verifying key for a specific circuit:

```rust
let common = CommonPreprocessedInput::from_constraint_system(&system, &ORDER_R_MINUS_1_ROOT_UNITY);
let srs = test_srs(common.n);
let kzg = KZG::new(srs); // The commitment scheme for plonk.
let vk = setup(&common, &kzg);
```

## Generating a proof
```rust
let inputs = HashMap::from([(x, FieldElement::from(4)), (e, FieldElement::from(3))]);
let assignments = system.solve(inputs).unwrap();
let witness = Witness::new(assignments, &system);

let public_inputs = system.public_input_values(&assignments);
let prover = Prover::new(kzg.clone(), TestRandomFieldGenerator {});
let proof = prover.prove(&witness, &public_inputs, &common, &vk);
```

## Verifying a proof
```rust
let verifier = Verifier::new(kzg);
assert!(verifier.verify(&proof, &public_inputs, &common, &vk));
```
