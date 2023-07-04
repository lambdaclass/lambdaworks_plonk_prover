use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkGroup, measurement::WallTime};
use lambdaworks_math::elliptic_curve::short_weierstrass::curves::bls12_381::default_types::{FrElement, FrField};
use lambdaworks_plonk::{
    prover::Prover,
    setup::{setup, VerificationKey, Witness, CommonPreprocessedInput},
    test_utils::{circuit_json::common_preprocessed_input_from_json, utils::G1Point},
    test_utils::utils::{test_srs, TestRandomFieldGenerator, KZG},
    verifier::Verifier,
};
use std::time::Duration;
use std::fs;

fn plonk_benches(c: &mut Criterion) {
    let mut group = c.benchmark_group("Plonk");
    group.sample_size(10);
    group.measurement_time(Duration::from_secs(30));

    // run_bench(&mut group, "square_and_multiply_2.json");
    // run_bench(&mut group, "square_and_multiply_8.json");
    run_bench(&mut group, "square_and_multiply_32.json");
}

fn run_bench(group: &mut BenchmarkGroup<WallTime>, circuit_name: &str) {
    const CARGO_DIR: &str = env!("CARGO_MANIFEST_DIR");
    const PROGRAM_BASE_REL_PATH: &str = "/benches/plonk_circuits/";
    let program_base_path = CARGO_DIR.to_string() + PROGRAM_BASE_REL_PATH;
    let program_path = program_base_path + circuit_name;
    
    let json_circuit = fs::read_to_string(program_path).unwrap();
    println!("Generando cosas");
    let (witness, common_preprocessed_input, public_input) =
        common_preprocessed_input_from_json(&json_circuit);
    println!("{:?}", common_preprocessed_input.n);
    let srs = test_srs(common_preprocessed_input.n);

    let kzg = KZG::new(srs);
    let verifying_key = setup(&common_preprocessed_input, &kzg);
    let random_generator = TestRandomFieldGenerator {};

    group.bench_function(circuit_name, |bench| {
        bench.iter(|| black_box(prove_plonk_circuit(
            &kzg,
            &witness,
            &public_input,
            &common_preprocessed_input,
            &verifying_key,
            &random_generator
        )));
    });
}

fn prove_plonk_circuit(
    kzg: &KZG,
    witness: &Witness<FrField>,
    public_input: &[FrElement],
    common_preprocessed_input: &CommonPreprocessedInput<FrField>,
    verifying_key: &VerificationKey<G1Point>,
    random_generator: &TestRandomFieldGenerator
) {
    let prover = Prover::new(kzg.clone(), random_generator.clone());
    let proof = prover.prove(
        &witness,
        &public_input,
        &common_preprocessed_input,
        verifying_key,
    );

    let verifier = Verifier::new(kzg.clone());
    assert!(verifier.verify(
        &proof,
        &public_input,
        &common_preprocessed_input,
        verifying_key
    ));
}

criterion_group!(benches, plonk_benches);
criterion_main!(benches);

