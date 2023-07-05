use criterion::{
    black_box, criterion_group, criterion_main, measurement::WallTime, BenchmarkGroup, Criterion,
};
use lambdaworks_math::elliptic_curve::short_weierstrass::curves::bls12_381::default_types::{
    FrElement, FrField,
};
use lambdaworks_plonk::{
    prover::{Proof, Prover},
    setup::{setup, CommonPreprocessedInput, VerificationKey, Witness},
    test_utils::utils::{test_srs, TestRandomFieldGenerator, KZG},
    test_utils::{circuit_json::common_preprocessed_input_from_json, utils::G1Point},
};
use std::fs;
use std::time::Duration;

fn plonk_benches(c: &mut Criterion) {
    let mut group = c.benchmark_group("Plonk");
    group.sample_size(10);
    group.measurement_time(Duration::from_secs(30));

    run_bench(&mut group, "square_and_multiply_32.json");
    run_bench(&mut group, "square_and_multiply_2048.json");
}

fn run_bench(group: &mut BenchmarkGroup<WallTime>, circuit_name: &str) {
    const CARGO_DIR: &str = env!("CARGO_MANIFEST_DIR");
    const PROGRAM_BASE_REL_PATH: &str = "/benches/plonk_circuits/";
    let program_base_path = CARGO_DIR.to_string() + PROGRAM_BASE_REL_PATH;
    let program_path = program_base_path + circuit_name;

    let json_circuit = fs::read_to_string(program_path).unwrap();
    let (witness, common_preprocessed_input, public_input) =
        common_preprocessed_input_from_json(&json_circuit);
    let srs = test_srs(common_preprocessed_input.n);
    let kzg = KZG::new(srs);
    let verifying_key = setup(&common_preprocessed_input, &kzg);
    let random_generator = TestRandomFieldGenerator {};

    group.bench_function(circuit_name, |bench| {
        bench.iter(|| {
            black_box(prove_plonk_circuit(
                black_box(&kzg),
                black_box(&witness),
                black_box(&public_input),
                black_box(&common_preprocessed_input),
                black_box(&verifying_key),
                black_box(&random_generator),
            ))
        });
    });
}

fn prove_plonk_circuit(
    kzg: &KZG,
    witness: &Witness<FrField>,
    public_input: &[FrElement],
    common_preprocessed_input: &CommonPreprocessedInput<FrField>,
    verifying_key: &VerificationKey<G1Point>,
    random_generator: &TestRandomFieldGenerator,
) -> Proof<FrField, KZG> {
    let prover = Prover::new(kzg.clone(), random_generator.clone());
    prover.prove(
        &witness,
        &public_input,
        &common_preprocessed_input,
        verifying_key,
    )
}

criterion_group!(benches, plonk_benches);
criterion_main!(benches);
