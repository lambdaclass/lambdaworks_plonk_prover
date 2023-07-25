# Lambdaworks Plonk Prover
A fast implementation of the Plonk zk-protocol written in Rust. This is part of the [Lambdaworks](https://github.com/lambdaclass/lambdaworks) zero-knowledge framework. It comes with a high-level API to build your own circuits.

<div>

[![Telegram Chat][tg-badge]][tg-url]

[tg-badge]: https://img.shields.io/static/v1?color=green&logo=telegram&label=chat&style=flat&message=join
[tg-url]: https://t.me/+98Whlzql7Hs0MDZh

</div>

## Building a custom circuit
The following code creates a circuit with two public inputs `x`, `y` and asserts `x*e=y`:

```rust
let system = &mut ConstraintSystem::<FrField>::new();
let x = system.new_public_input();
let y = system.new_public_input();
let e = system.new_variable();

let z = system.mul(&x, &e);    
system.assert_eq(&y, &z);;
```

## Generating a proof
### Setup
A setup is needed in order to generate a proof for a new circuit. This generates a verifying key that will be used by both the prover and the verifier:

```rust
let common = CommonPreprocessedInput::from_constraint_system(&system, &ORDER_R_MINUS_1_ROOT_UNITY);
let srs = test_srs(common.n);
let kzg = KZG::new(srs); // The commitment scheme for plonk.
let verifying_key = setup(&common, &kzg);
```

### Prover
First, we fix the public inputs `x` and `y` and solve the constraint system:
```rust
let inputs = HashMap::from([(x, FieldElement::from(4)), (e, FieldElement::from(3))]);
let assignments = system.solve(inputs).unwrap();
```

Finally, we call the prover:
```rust
let witness = Witness::new(assignments, &system);
let public_inputs = system.public_input_values(&assignments);
let prover = Prover::new(kzg.clone(), TestRandomFieldGenerator {});
let proof = prover.prove(&witness, &public_inputs, &common, &verifying_key);
```

## Verifying a proof
Just call the verifier:

```rust
let verifier = Verifier::new(kzg);
assert!(verifier.verify(&proof, &public_inputs, &common, &verifying_key));
```
