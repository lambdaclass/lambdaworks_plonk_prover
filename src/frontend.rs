use lambdaworks_math::field::{
    element::FieldElement,
    traits::{IsField, IsPrimeField},
};
use std::collections::HashMap;

// a Ql + b Qr + a b Qm + c Qo + Qc = 0
struct ConstraintType<F: IsField> {
    ql: FieldElement<F>,
    qr: FieldElement<F>,
    qm: FieldElement<F>,
    qo: FieldElement<F>,
    qc: FieldElement<F>,
}

// a Ql + b Qr + a b Qm + c Qo + Qc = 0
enum Column {
    L,
    R,
    O,
}

struct PlonkConstraint<F: IsField> {
    constraint_type: ConstraintType<F>,
    hint: Option<(fn(&FieldElement<F>) -> FieldElement<F>, Column, Column)>, // func, input, output
    l: usize,
    r: usize,
    o: usize,
}

struct ConstraintSystem<F: IsField> {
    num_variables: usize,
    constraints: Vec<PlonkConstraint<F>>,
}

impl<F> ConstraintSystem<F>
where
    F: IsField,
{
    fn new() -> Self {
        Self {
            num_variables: 0,
            constraints: Vec::new(),
        }
    }

    fn empty_wire(&self) -> usize {
        0
    }

    fn new_wire(&mut self) -> usize {
        let variable_id = self.num_variables;
        self.num_variables += 1;
        variable_id
    }

    fn add_constraint(&mut self, constraint: PlonkConstraint<F>) {
        self.constraints.push(constraint);
    }
}

struct Variable(usize);

impl Variable {
    fn new<F: IsField>(constraint_system: &mut ConstraintSystem<F>) -> Self {
        Variable(constraint_system.new_wire())
    }

    fn add<F: IsField>(
        &self,
        other: &Variable,
        constraint_system: &mut ConstraintSystem<F>,
    ) -> Self {
        let result = Self::new(constraint_system);
        constraint_system.add_constraint(PlonkConstraint {
            constraint_type: ConstraintType {
                ql: FieldElement::one(),
                qr: FieldElement::one(),
                qm: FieldElement::zero(),
                qo: -FieldElement::one(),
                qc: FieldElement::zero(),
            },
            l: self.0,
            r: other.0,
            o: result.0,
            hint: None,
        });
        result
    }

    fn mul<F: IsField>(
        &self,
        other: &Variable,
        constraint_system: &mut ConstraintSystem<F>,
    ) -> Self {
        let result = Self::new(constraint_system);
        constraint_system.add_constraint(PlonkConstraint {
            constraint_type: ConstraintType {
                ql: FieldElement::zero(),
                qr: FieldElement::zero(),
                qm: FieldElement::one(),
                qo: -FieldElement::one(),
                qc: FieldElement::zero(),
            },
            l: self.0,
            r: other.0,
            o: result.0,
            hint: None,
        });
        result
    }

    // TODO: check 0.div(0) does not compile
    fn div<F: IsField>(&self, other: &Self, constraint_system: &mut ConstraintSystem<F>) -> Self {
        let result = Self::new(constraint_system);
        constraint_system.add_constraint(PlonkConstraint {
            constraint_type: ConstraintType {
                ql: FieldElement::zero(),
                qr: FieldElement::zero(),
                qm: FieldElement::one(),
                qo: -FieldElement::one(),
                qc: FieldElement::zero(),
            },
            l: result.0,
            r: other.0,
            o: self.0,
            hint: None,
        });
        result
    }

    fn add_constant<F: IsField>(
        &self,
        constant: FieldElement<F>,
        constraint_system: &mut ConstraintSystem<F>,
    ) -> Self {
        let result = Self::new(constraint_system);
        constraint_system.add_constraint(PlonkConstraint {
            constraint_type: ConstraintType {
                ql: FieldElement::one(),
                qr: FieldElement::zero(),
                qm: FieldElement::zero(),
                qo: -FieldElement::one(),
                qc: constant,
            },
            l: self.0,
            r: constraint_system.empty_wire(),
            o: result.0,
            hint: None,
        });
        result
    }

    fn new_boolean<F: IsField>(constraint_system: &mut ConstraintSystem<F>) -> Self {
        let boolean = Self::new(constraint_system);
        constraint_system.add_constraint(PlonkConstraint {
            constraint_type: ConstraintType {
                ql: -FieldElement::one(),
                qr: FieldElement::zero(),
                qm: FieldElement::one(),
                qo: FieldElement::zero(),
                qc: FieldElement::zero(),
            },
            l: boolean.0,
            r: boolean.0,
            o: constraint_system.empty_wire(),
            hint: None,
        });
        boolean
    }

    fn new_u32<F: IsPrimeField>(
        v: &Variable,
        constraint_system: &mut ConstraintSystem<F>,
    ) -> Vec<Self> {
        let hint = |v: &FieldElement<F>| {
            if v.representative() & 1.into() == 1.into() {
                FieldElement::one()
            } else {
                FieldElement::zero()
            }
        };
        let bits: Vec<_> = (0..32)
            .map(|_| Self::new_boolean(constraint_system))
            .collect();
        let mut aux_vars: Vec<Variable> = Vec::new();

        let t_0 = Self::new(constraint_system);
        constraint_system.add_constraint(PlonkConstraint {
            constraint_type: ConstraintType {
                ql: FieldElement::from(2),
                qr: FieldElement::one(),
                qm: FieldElement::zero(),
                qo: -FieldElement::one(),
                qc: FieldElement::zero(),
            },
            l: bits[0].0,
            r: bits[1].0,
            o: t_0.0,
            hint: Some((hint, Column::O, Column::R)),
        });
        aux_vars.push(t_0);
        for i in 2..32 {
            let t_i = Self::new(constraint_system);
            constraint_system.add_constraint(PlonkConstraint {
                constraint_type: ConstraintType {
                    ql: FieldElement::from(2),
                    qr: FieldElement::one(),
                    qm: FieldElement::zero(),
                    qo: -FieldElement::one(),
                    qc: FieldElement::zero(),
                },
                l: aux_vars.last().unwrap().0,
                r: bits[i].0,
                o: t_i.0,
                hint: Some((hint, Column::O, Column::R)),
            });
            aux_vars.push(t_i);
        }
        Self::assert_eq(v, aux_vars.last().unwrap(), constraint_system);
        bits
    }

    fn not<F: IsField>(&self, constraint_system: &mut ConstraintSystem<F>) -> Self {
        let result = Self::new(constraint_system);
        constraint_system.add_constraint(PlonkConstraint {
            constraint_type: ConstraintType {
                ql: FieldElement::one(),
                qr: FieldElement::one(),
                qm: FieldElement::zero(),
                qo: FieldElement::zero(),
                qc: -FieldElement::one(),
            },
            l: self.0,
            r: result.0,
            o: constraint_system.empty_wire(),
            hint: None,
        });
        result
    }

    fn inv<F: IsField>(v: &Self, constraint_system: &mut ConstraintSystem<F>) -> (Self, Self) {
        let is_zero = Self::new(constraint_system);
        let v_inverse = Self::new(constraint_system);
        // v * z == 0
        constraint_system.add_constraint(PlonkConstraint {
            constraint_type: ConstraintType {
                ql: FieldElement::zero(),
                qr: FieldElement::zero(),
                qm: FieldElement::one(),
                qo: FieldElement::zero(),
                qc: FieldElement::zero(),
            },
            l: v.0,
            r: is_zero.0,
            o: constraint_system.empty_wire(),
            hint: Some((
                |v: &FieldElement<F>| {
                    if *v == FieldElement::zero() {
                        FieldElement::one()
                    } else {
                        FieldElement::zero()
                    }
                },
                Column::L,
                Column::R,
            )),
        });
        // v * w + z == 1
        constraint_system.add_constraint(PlonkConstraint {
            constraint_type: ConstraintType {
                ql: FieldElement::zero(),
                qr: FieldElement::zero(),
                qm: FieldElement::one(),
                qo: FieldElement::one(),
                qc: -FieldElement::one(),
            },
            l: v.0,
            r: v_inverse.0, // w
            o: is_zero.0,   // z
            hint: Some((
                |v: &FieldElement<F>| {
                    if *v == FieldElement::zero() {
                        FieldElement::zero()
                    } else {
                        v.inv()
                    }
                },
                Column::L,
                Column::R,
            )),
        });
        (is_zero, v_inverse)
    }

    fn assert_eq<F: IsField>(v1: &Self, v2: &Self, constraint_system: &mut ConstraintSystem<F>) {
        constraint_system.add_constraint(PlonkConstraint {
            constraint_type: ConstraintType {
                ql: FieldElement::one(),
                qr: -FieldElement::one(),
                qm: FieldElement::zero(),
                qo: FieldElement::zero(),
                qc: FieldElement::zero(),
            },
            l: v1.0,
            r: v2.0,
            o: constraint_system.empty_wire(),
            hint: None,
        });
    }

    fn if_else<F: IsField>(
        boolean_condition: &Self,
        v1: &Self,
        v2: &Self,
        constraint_system: &mut ConstraintSystem<F>,
    ) -> Self {
        let if_branch = v1.mul(&boolean_condition, constraint_system);
        let else_branch = v2.mul(&boolean_condition.not(constraint_system), constraint_system);
        if_branch.add(&else_branch, constraint_system)
    }

    fn if_neq_else<F: IsField>(
        condition: &Self,
        v1: &Self,
        v2: &Self,
        constraint_system: &mut ConstraintSystem<F>,
    ) -> Self {
        let (is_zero, _) = Self::inv(condition, constraint_system);
        Self::if_else(&is_zero, v2, v1, constraint_system)
    }
}

fn solver<F: IsField>(
    constraint_system: &ConstraintSystem<F>,
    assignments: &mut HashMap<usize, FieldElement<F>>,
) -> Result<(), ()> {
    let mut number_solved = 0;
    let mut checked_constraints = vec![false; constraint_system.constraints.len()];
    loop {
        let old_solved = number_solved;
        for (i, constraint) in constraint_system.constraints.iter().enumerate() {
            let ct = &constraint.constraint_type;
            let has_l = assignments.contains_key(&constraint.l);
            let has_r = assignments.contains_key(&constraint.r);
            let has_o = assignments.contains_key(&constraint.o);

            if let Some((hint, input_col, output_col)) = &constraint.hint {
                match (input_col, output_col, has_l, has_r, has_o) {
                    (Column::L, Column::R, true, false, _) => {
                        assignments
                            .insert(constraint.r, hint(assignments.get(&constraint.l).unwrap()));
                        number_solved += 1;
                    }
                    (Column::L, Column::O, true, _, false) => {
                        assignments
                            .insert(constraint.o, hint(assignments.get(&constraint.l).unwrap()));
                        number_solved += 1;
                    }
                    (Column::R, Column::L, false, true, _) => {
                        assignments
                            .insert(constraint.l, hint(assignments.get(&constraint.r).unwrap()));
                        number_solved += 1;
                    }
                    (Column::R, Column::O, _, true, false) => {
                        assignments
                            .insert(constraint.o, hint(assignments.get(&constraint.r).unwrap()));
                        number_solved += 1;
                    }
                    (Column::O, Column::L, false, _, true) => {
                        assignments
                            .insert(constraint.l, hint(assignments.get(&constraint.o).unwrap()));
                        number_solved += 1;
                    }
                    (Column::O, Column::R, _, false, true) => {
                        assignments
                            .insert(constraint.r, hint(assignments.get(&constraint.o).unwrap()));
                        number_solved += 1;
                    }
                    _ => {}
                }
            }

            // a Ql + b Qr + a b Qm + c Qo + Qc = 0
            if has_l && has_r && has_o {
                continue;
            } else if has_l && has_r {
                let a = assignments.get(&constraint.l).unwrap();
                let b = assignments.get(&constraint.r).unwrap();
                let mut c = a * &ct.ql + b * &ct.qr + a * b * &ct.qm + &ct.qc;
                if ct.qo == FieldElement::zero() {
                    continue;
                }
                c = -c * ct.qo.inv();
                assignments.insert(constraint.o, c);
            } else if has_l && has_o {
                let a = assignments.get(&constraint.l).unwrap();
                let c = assignments.get(&constraint.o).unwrap();
                let mut b = a * &ct.ql + c * &ct.qo + &ct.qc;
                let denominator = &ct.qr + a * &ct.qm;
                if denominator == FieldElement::zero() {
                    continue;
                }
                b = -b * denominator.inv();
                assignments.insert(constraint.r, b);
            } else if has_r && has_o {
                let b = assignments.get(&constraint.r).unwrap();
                let c = assignments.get(&constraint.o).unwrap();
                let mut a = b * &ct.qr + c * &ct.qo + &ct.qc;
                let denominator = &ct.ql + b * &ct.qm;
                if denominator == FieldElement::zero() {
                    continue;
                }
                a = -a * denominator.inv();
                assignments.insert(constraint.l, a);
            } else {
                continue;
            }
            checked_constraints[i] = true;
            number_solved = number_solved + 1;
        }
        if number_solved == old_solved {
            break;
        }
    }
    for (constraint, checked) in constraint_system
        .constraints
        .iter()
        .zip(checked_constraints.iter())
    {
        if !checked {
            let a = assignments.get(&constraint.l);
            let b = assignments.get(&constraint.r);
            let c = assignments.get(&constraint.o);

            match (a, b, c) {
                (Some(a), Some(b), Some(c)) => {
                    let ct = &constraint.constraint_type;
                    let result = a * &ct.ql + b * &ct.qr + a * b * &ct.qm + c * &ct.qo + &ct.qc;
                    if result != FieldElement::zero() {
                        return Err(());
                    }
                }
                _ => return Err(()),
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use lambdaworks_math::field::{element::FieldElement, fields::u64_prime_field::U64PrimeField};

    // assert out == if(i1^2 + i1 * i2 + 5 != 0, i1, i2)
    #[test]
    fn test_constraint_system() {
        let constraint_system = &mut ConstraintSystem::<U64PrimeField<17>>::new();

        let input1 = Variable::new(constraint_system);
        let input2 = Variable::new(constraint_system);
        let output = Variable::new(constraint_system);

        let z1 = input1.add(&input2, constraint_system);
        let z2 = z1.mul(&input1, constraint_system);
        let z3 = z2.add_constant(FieldElement::from(5), constraint_system);
        let z4 = Variable::if_else(&z3, &input1, &input2, constraint_system);
        Variable::assert_eq(&z4, &output, constraint_system);

        println!("NUM WIRES: {}", constraint_system.num_variables);
    }

    /*
        fn (input1, input2)
            z1 = input1 + input2;
            z2 = z1 * input1;
            z3 = z2 + 5;

        Constraints:
        Ql Qr Qm Qo Qc
         1  1  0 -1  0
         0  0  1 -1  0
         1  0  0 -1  5

        Wirings:
         A  B  C
         0  1  2
         0  2  3
         3  0  4

        Result:
         A  B  C
         1  2  3
         1  3  3
         3  0  8

        Assignemnt:
        0 -> 1
        1 -> 2
        2 -> 3
        3 -> 3
        4 -> 8
    */
    #[test]
    fn test_solve_1() {
        let constraint_system = &mut ConstraintSystem::<U64PrimeField<17>>::new();

        let input1 = Variable::new(constraint_system);
        let input2 = Variable::new(constraint_system);

        let z1 = input1.add(&input2, constraint_system);
        let z2 = z1.mul(&input1, constraint_system);
        z2.add_constant(FieldElement::from(5), constraint_system);

        let mut inputs = HashMap::from([(0, FieldElement::one()), (1, FieldElement::from(2))]);

        solver(&constraint_system, &mut inputs).unwrap();

        // println!("Assignment");
        // println!("{:?}", inputs);
    }

    /*
        fn (input1, input2, output):
            z1 = input1 + input2;
            z2 = z1 * input1;
            z3 = z2 + 5;
            z4 = z3 != 0? input1 : input2;
            z4 == output;

        Assigment:
            0 -> input1 -> 2
            1 -> input2 -> 3
            2 -> z1     -> 5
            3 -> z2     -> 10
            4 -> z3     -> 15
            5 -> z4     ->    ?? Acá ya agrega más vars internamente

    */
    #[test]
    fn test_solve_2() {
        let constraint_system = &mut ConstraintSystem::<U64PrimeField<17>>::new();

        let input1 = Variable::new(constraint_system);
        let input2 = Variable::new(constraint_system);
        let output = Variable::new(constraint_system);

        let z1 = input1.add(&input2, constraint_system);
        let z2 = z1.mul(&input1, constraint_system);
        let z3 = z2.add_constant(FieldElement::from(5), constraint_system);
        let z4 = Variable::if_else(&z3, &input1, &input2, constraint_system);
        Variable::assert_eq(&z4, &output, constraint_system);
        let mut inputs =
            HashMap::from([(0, FieldElement::from(2u64)), (1, FieldElement::from(3u64))]);

        solver(&constraint_system, &mut inputs).unwrap();

        // println!("Assignment");
        // println!("{:?}", inputs);
    }

    #[test]
    fn test_solve_u32() {
        let constraint_system = &mut ConstraintSystem::<U64PrimeField<17>>::new();

        let input = Variable::new(constraint_system);
        let u32_var = Variable::new_u32(&input, constraint_system);

        let input_assignment = 13;
        let mut inputs = HashMap::from([(0, FieldElement::from(input_assignment))]);

        solver(&constraint_system, &mut inputs).unwrap();

        for i in 0..32 {
            assert_eq!(
                inputs.get(&u32_var[i].0).unwrap().representative(),
                (input_assignment >> (31 - i)) & 1
            );
        }
    }

    #[test]
    fn test_pow() {
        let constraint_system = &mut ConstraintSystem::<U64PrimeField<65537>>::new();

        let base = Variable::new(constraint_system);
        let exponent = Variable::new(constraint_system);
        let exponent_bits = Variable::new_u32(&exponent, constraint_system);
        let mut result = Variable::new(constraint_system);
        let result_first_value_id = result.0;

        assert_eq!(exponent_bits.len(), 32);
        for i in 0..32 {
            if i != 0 {
                result = result.mul(&result, constraint_system);
            }
            result = Variable::if_else(
                &exponent_bits[i],
                &result.mul(&base, constraint_system),
                &result,
                constraint_system,
            );
        }
        let mut inputs = HashMap::from([
            (base.0, FieldElement::from(3)),
            (exponent.0, FieldElement::from(10)),
            (result_first_value_id, FieldElement::from(1)),
        ]);

        solver(&constraint_system, &mut inputs).unwrap();
        assert_eq!(inputs.get(&result.0).unwrap(), &FieldElement::from(59049));
        println!("{:?}", constraint_system.num_variables);
    }

    #[test]
    fn test_solve_3() {
        let constraint_system = &mut ConstraintSystem::<U64PrimeField<17>>::new();

        let input1 = Variable::new(constraint_system);
        let input2 = Variable::new(constraint_system);

        let z = Variable::if_else(&input1, &input1, &input2, constraint_system);
        let mut inputs = HashMap::from([
            (0, FieldElement::from(0u64)),
            (1, FieldElement::from(16u64)),
        ]);

        solver(&constraint_system, &mut inputs).unwrap();

        // println!("Assignment");
        // println!("{:?}", inputs);
    }
}
