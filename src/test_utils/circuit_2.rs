use super::utils::{
    generate_domain, generate_permutation_coefficients, ORDER_R_MINUS_1_ROOT_UNITY, generate_permutation_polynomials,
};
use crate::setup::{CommonPreprocessedInput, Witness};
use lambdaworks_math::{
    elliptic_curve::short_weierstrass::curves::bls12_381::default_types::{FrElement, FrField},
    field::{element::FieldElement, traits::IsFFTField},
    polynomial::Polynomial,
};

pub const ORDER_8_ROOT_UNITY: FrElement = FrElement::from_hex_unchecked(
    "345766f603fa66e78c0625cd70d77ce2b38b21c28713b7007228fd3397743f7a",
); // order 8

/*  Test circuit for the program:
    public input x
    public input y
    private input e
    z1 = x * e
    z2 = z1 + 5
    assert y == z2
*/
pub fn test_common_preprocessed_input_2() -> CommonPreprocessedInput<FrField> {
    let n: usize = 8;
    let omega = FrField::get_primitive_root_of_unity(3).unwrap();
    let domain = generate_domain(&omega, n);
    let permutation = &[
        23, 4, 0, 18, 1, 2, 5, 6, 7, 8, 10, 9, 19, 11, 13, 14, 15, 16, 3, 12, 17, 20, 21, 22,
    ]; // TODO: Add missing permutation for test to pass (Probably could be all additional numbers that don't belong to any cycle
    // e.g: The identity 
    let permuted =
        generate_permutation_coefficients(3, &omega, n, permutation, &ORDER_R_MINUS_1_ROOT_UNITY);

    let (s_i_lagrange, s_i) = generate_permutation_polynomials(3, n, &permuted);

    CommonPreprocessedInput {
        n,
        m: 3,
        omega,
        k1: ORDER_R_MINUS_1_ROOT_UNITY,
        domain: domain.clone(),

        ql: Polynomial::interpolate(
            &domain,
            &[
                -FieldElement::one(),
                -FieldElement::one(),
                FieldElement::zero(),
                FieldElement::one(),
                FieldElement::one(),
                FieldElement::zero(),
                FieldElement::zero(),
                FieldElement::zero(),
            ],
        )
        .unwrap(),
        qr: Polynomial::interpolate(
            &domain,
            &[
                FieldElement::zero(),
                FieldElement::zero(),
                FieldElement::zero(),
                FieldElement::zero(),
                -FieldElement::one(),
                FieldElement::zero(),
                FieldElement::zero(),
                FieldElement::zero(),
            ],
        )
        .unwrap(),
        qo: Polynomial::interpolate(
            &domain,
            &[
                FieldElement::zero(),
                FieldElement::zero(),
                -FieldElement::one(),
                -FieldElement::one(),
                FieldElement::zero(),
                FieldElement::zero(),
                FieldElement::zero(),
                FieldElement::zero(),
            ],
        )
        .unwrap(),
        qm: Polynomial::interpolate(
            &domain,
            &[
                FieldElement::zero(),
                FieldElement::zero(),
                FieldElement::one(),
                FieldElement::zero(),
                FieldElement::zero(),
                FieldElement::zero(),
                FieldElement::zero(),
                FieldElement::zero(),
            ],
        )
        .unwrap(),
        qc: Polynomial::interpolate(
            &domain,
            &[
                FieldElement::zero(),
                FieldElement::zero(),
                FieldElement::zero(),
                FieldElement::from(5_u64),
                FieldElement::zero(),
                FieldElement::zero(),
                FieldElement::zero(),
                FieldElement::zero(),
            ],
        )
        .unwrap(),

        s_i_lagrange:s_i_lagrange,
        s_i:s_i
    }
}

pub fn test_witness_2(x: FrElement, e: FrElement) -> Witness<FrField> {
    Witness {
        a: vec![
            x.clone(),
            &x * &e + FieldElement::from(5_u64),
            x.clone(),
            &x * &e,
            &x * &e + FieldElement::from(5_u64),
            x.clone(),
            x.clone(),
            x.clone(),
        ],
        b: vec![
            x.clone(),
            x.clone(),
            e.clone(),
            x.clone(),
            &x * &e + FieldElement::from(5_u64),
            x.clone(),
            x.clone(),
            x.clone(),
        ],
        c: vec![
            x.clone(),
            x.clone(),
            &x * &e,
            &x * &e + FieldElement::from(5_u64),
            x.clone(),
            x.clone(),
            x.clone(),
            x,
        ],
        lookup_columns: Vec::new()
    }
}
