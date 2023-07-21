use std::collections::HashMap;

use crate::frontend::{get_permutation, ConstraintSystem, Variable};
use crate::test_utils::utils::{
    generate_domain, generate_permutation_coefficients,
};
use lambdaworks_crypto::commitments::traits::IsCommitmentScheme;
use lambdaworks_crypto::fiat_shamir::default_transcript::DefaultTranscript;
use lambdaworks_crypto::fiat_shamir::transcript::Transcript;
use lambdaworks_math::fft::polynomial::FFTPoly;
use lambdaworks_math::field::traits::IsFFTField;
use lambdaworks_math::field::{element::FieldElement, traits::IsField};
use lambdaworks_math::polynomial::Polynomial;
use lambdaworks_math::traits::{ByteConversion, Serializable};

// TODO: implement getters
pub struct Witness<F: IsField> {
    pub a: Vec<FieldElement<F>>,
    pub b: Vec<FieldElement<F>>,
    pub c: Vec<FieldElement<F>>,
}

impl<F: IsField> Witness<F> {
    pub fn new(
        system: &ConstraintSystem<F>,
        inputs: &HashMap<Variable, FieldElement<F>>,
        length: usize,
    ) -> Self {
        let mut a = Vec::with_capacity(length);
        let mut b = Vec::with_capacity(length);
        let mut c = Vec::with_capacity(length);

        // Public input header
        for constraint in system.public_input_header().iter() {
            a.push(inputs[&constraint.l].clone());
            b.push(inputs[&constraint.r].clone());
            c.push(inputs[&constraint.o].clone());
        }

        // Body
        for constraint in system.constraints.iter() {
            a.push(inputs[&constraint.l].clone());
            b.push(inputs[&constraint.r].clone());
            c.push(inputs[&constraint.o].clone());
        }

        // Padding
        let padding_constraint = system.padding_constraint();
        let pad_length = length - a.len();
        for _ in 0..pad_length {
            a.push(inputs[&padding_constraint.l].clone());
            b.push(inputs[&padding_constraint.r].clone());
            c.push(inputs[&padding_constraint.o].clone());
        }

        Self { a, b, c }
    }
}

// TODO: implement getters
#[derive(Clone)]
pub struct CommonPreprocessedInput<F: IsField> {
    pub n: usize,
    /// Number of constraints
    pub domain: Vec<FieldElement<F>>,
    pub omega: FieldElement<F>,
    pub k1: FieldElement<F>,

    pub ql: Polynomial<FieldElement<F>>,
    pub qr: Polynomial<FieldElement<F>>,
    pub qo: Polynomial<FieldElement<F>>,
    pub qm: Polynomial<FieldElement<F>>,
    pub qc: Polynomial<FieldElement<F>>,

    pub s1: Polynomial<FieldElement<F>>,
    pub s2: Polynomial<FieldElement<F>>,
    pub s3: Polynomial<FieldElement<F>>,

    pub s1_lagrange: Vec<FieldElement<F>>,
    pub s2_lagrange: Vec<FieldElement<F>>,
    pub s3_lagrange: Vec<FieldElement<F>>,
}

impl<F: IsFFTField> CommonPreprocessedInput<F> {
    pub fn from_constraint_system(
        system: &ConstraintSystem<F>,
        order_r_minus_1_root_unity: &FieldElement<F>,
    ) -> Self {
        let header = system.public_input_header();
        let body = &system.constraints;
        let total_length = (header.len() + body.len()).next_power_of_two();
        let pad =
            vec![system.padding_constraint(); total_length - header.len() - body.len()];

        let mut full_constraints = header;
        full_constraints.extend_from_slice(body);
        full_constraints.extend_from_slice(&pad);

        let n = full_constraints.len();
        let omega = F::get_primitive_root_of_unity(n.trailing_zeros() as u64).unwrap();
        let domain = generate_domain(&omega, n);

        let n_constraints = full_constraints.len();
        let mut lro = vec![system.null_variable(); n_constraints * 3];

        // Make a single vector with | a_1 .. a_m | b_1 .. b_m | c_1 .. c_m | concatenated.
        for (index, constraint) in full_constraints.iter().enumerate() {
            lro[index] = constraint.l;
            lro[index + n_constraints] = constraint.r;
            lro[index + n_constraints * 2] = constraint.o;
        }

        let permutation = get_permutation(&lro);
        let permuted =
            generate_permutation_coefficients(&omega, n, &permutation, order_r_minus_1_root_unity);

        let s1_lagrange: Vec<FieldElement<F>> = permuted[..n].to_vec();
        let s2_lagrange: Vec<FieldElement<F>> = permuted[n..2 * n].to_vec();
        let s3_lagrange: Vec<FieldElement<F>> = permuted[2 * n..].to_vec();

        let mut ql = Vec::new();
        let mut qr = Vec::new();
        let mut qm = Vec::new();
        let mut qo = Vec::new();
        let mut qc = Vec::new();

        // Add constraints
        for constraint in full_constraints.iter() {
            ql.push(constraint.constraint_type.ql.clone());
            qr.push(constraint.constraint_type.qr.clone());
            qm.push(constraint.constraint_type.qm.clone());
            qo.push(constraint.constraint_type.qo.clone());
            qc.push(constraint.constraint_type.qc.clone());
        }

        Self {
            domain,
            n,
            omega,
            k1: order_r_minus_1_root_unity.clone(),
            ql: Polynomial::interpolate_fft(&ql).unwrap(), // TODO: Remove unwraps
            qr: Polynomial::interpolate_fft(&qr).unwrap(),
            qo: Polynomial::interpolate_fft(&qo).unwrap(),
            qm: Polynomial::interpolate_fft(&qm).unwrap(),
            qc: Polynomial::interpolate_fft(&qc).unwrap(),
            s1: Polynomial::interpolate_fft(&s1_lagrange).unwrap(),
            s2: Polynomial::interpolate_fft(&s2_lagrange).unwrap(),
            s3: Polynomial::interpolate_fft(&s3_lagrange).unwrap(),
            s1_lagrange,
            s2_lagrange,
            s3_lagrange,
        }
    }
}

#[allow(unused)]
pub struct VerificationKey<G1Point> {
    pub qm_1: G1Point,
    pub ql_1: G1Point,
    pub qr_1: G1Point,
    pub qo_1: G1Point,
    pub qc_1: G1Point,

    pub s1_1: G1Point,
    pub s2_1: G1Point,
    pub s3_1: G1Point,
}

#[allow(unused)]
pub fn setup<F: IsField, CS: IsCommitmentScheme<F>>(
    common_input: &CommonPreprocessedInput<F>,
    commitment_scheme: &CS,
) -> VerificationKey<CS::Commitment> {
    VerificationKey {
        qm_1: commitment_scheme.commit(&common_input.qm),
        ql_1: commitment_scheme.commit(&common_input.ql),
        qr_1: commitment_scheme.commit(&common_input.qr),
        qo_1: commitment_scheme.commit(&common_input.qo),
        qc_1: commitment_scheme.commit(&common_input.qc),

        s1_1: commitment_scheme.commit(&common_input.s1),
        s2_1: commitment_scheme.commit(&common_input.s2),
        s3_1: commitment_scheme.commit(&common_input.s3),
    }
}

pub fn new_strong_fiat_shamir_transcript<F, CS>(
    vk: &VerificationKey<CS::Commitment>,
    public_input: &[FieldElement<F>],
) -> DefaultTranscript
where
    F: IsField,
    FieldElement<F>: ByteConversion,
    CS: IsCommitmentScheme<F>,
    CS::Commitment: Serializable,
{
    let mut transcript = DefaultTranscript::new();

    transcript.append(&vk.s1_1.serialize());
    transcript.append(&vk.s2_1.serialize());
    transcript.append(&vk.s3_1.serialize());
    transcript.append(&vk.ql_1.serialize());
    transcript.append(&vk.qr_1.serialize());
    transcript.append(&vk.qm_1.serialize());
    transcript.append(&vk.qo_1.serialize());
    transcript.append(&vk.qc_1.serialize());

    for value in public_input.iter() {
        transcript.append(&value.to_bytes_be());
    }
    transcript
}

#[cfg(test)]
mod tests {
    use lambdaworks_math::elliptic_curve::short_weierstrass::curves::bls12_381::default_types::FrField;
    use lambdaworks_math::elliptic_curve::{
        short_weierstrass::curves::bls12_381::curve::BLS12381Curve, traits::IsEllipticCurve,
    };

    use super::*;
    use crate::test_utils::circuit_1::test_common_preprocessed_input_1;
    use crate::test_utils::utils::{test_srs, FpElement, KZG};

    #[test]
    fn setup_works_for_simple_circuit() {
        let common_input = test_common_preprocessed_input_1();
        let srs = test_srs(common_input.n);
        let kzg = KZG::new(srs);

        let vk = setup::<FrField, KZG>(&common_input, &kzg);

        let expected_ql = BLS12381Curve::create_point_from_affine(
            FpElement::from_hex_unchecked("1492341357755e31a6306abf3237f84f707ded7cb526b8ffd40901746234ef27f12bc91ef638e4977563db208b765f12"),
            FpElement::from_hex_unchecked("ec3ff8288ea339010658334f494a614f7470c19a08d53a9cf5718e0613bb65d2cdbc1df374057d9b45c35cf1f1b5b72"),
        ).unwrap();
        let expected_qr = BLS12381Curve::create_point_from_affine(
            FpElement::from_hex_unchecked("107ab09b6b8c6fc55087aeb8045e17a6d016bdacbc64476264328e71f3e85a4eacaee34ee963e9c9249b6b1bc9653674"),
            FpElement::from_hex_unchecked("f98e3fe5a53545b67a51da7e7a6cedc51af467abdefd644113fb97edf339aeaa5e2f6a5713725ec76754510b76a10be"),
        ).unwrap();
        let expected_qo = BLS12381Curve::create_point_from_affine(
            FpElement::from_hex_unchecked("9fd00baa112a0064ce5c3c2d243e657b25df8a2f237b91eec27e83157f6ca896a2401d07ec7d7d097d2f2a344e2018f"),
            FpElement::from_hex_unchecked("15922cfa65972d80823c6bb9aeb0637c864b636267bfee2818413e9cdc5f7948575c4ce097bb8b9db8087c4ed5056592"),
        ).unwrap();
        let expected_qm = BLS12381Curve::create_point_from_affine(
            FpElement::from_hex_unchecked("9fd00baa112a0064ce5c3c2d243e657b25df8a2f237b91eec27e83157f6ca896a2401d07ec7d7d097d2f2a344e2018f"),
            FpElement::from_hex_unchecked("46ee4efd3e8b919c8df3bfc949b495ade2be8228bc524974eef94041a517cdbc74fb31e1998746201f683b12afa4519"),
        ).unwrap();

        let expected_s1 = BLS12381Curve::create_point_from_affine(
            FpElement::from_hex_unchecked("187ee12de08728650d18912aa9fe54863922a9eeb37e34ff43041f1d039f00028ad2cdf23705e6f6ab7ea9406535c1b0"),
            FpElement::from_hex_unchecked("4f29051990de0d12b38493992845d9abcb48ef18239eca8b8228618c78ec371d39917bc0d45cf6dc4f79bd64baa9ae2")
        ).unwrap();
        let expected_s2 = BLS12381Curve::create_point_from_affine(
            FpElement::from_hex_unchecked("167c0384025887c01ea704234e813842a4acef7d765c3a94a5442ca685b4fc1d1b425ba7786a7413bd4a7d6a1eb5a35a"),
            FpElement::from_hex_unchecked("12b644100c5d00af27c121806c4779f88e840ff3fdac44124b8175a303d586c4d910486f909b37dda1505c485f053da1")
        ).unwrap();
        let expected_s3 = BLS12381Curve::create_point_from_affine(
            FpElement::from_hex_unchecked("188fb6dba3cf5af8a7f6a44d935bb3dd2083a5beb4c020f581739ebc40659c824a4ca8279cf7d852decfbca572e4fa0e"),
            FpElement::from_hex_unchecked("d84d52582fd95bfa7672f7cef9dd4d0b1b4a54d33f244fdb97df71c7d45fd5c5329296b633c9ed23b8475ee47b9d99")
        ).unwrap();

        assert_eq!(vk.ql_1, expected_ql);
        assert_eq!(vk.qr_1, expected_qr);
        assert_eq!(vk.qo_1, expected_qo);
        assert_eq!(vk.qm_1, expected_qm);

        assert_eq!(vk.s1_1, expected_s1);
        assert_eq!(vk.s2_1, expected_s2);
        assert_eq!(vk.s3_1, expected_s3);
    }
}
