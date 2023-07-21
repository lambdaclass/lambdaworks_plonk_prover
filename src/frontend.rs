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
#[derive(Clone)]
enum Column {
    L,
    R,
    O,
}

#[allow(unused)]
#[derive(Clone)]
struct Hint<F: IsField> {
    function: fn(&FieldElement<F>) -> FieldElement<F>,
    input: Column,
    output: Column,
}

#[allow(unused)]
type Variable = usize;

#[allow(unused)]
struct PlonkConstraint<F: IsField> {
    constraint_type: ConstraintType<F>,
    hint: Option<Hint<F>>,
    l: Variable,
    r: Variable,
    o: Variable,
}

#[allow(unused)]
struct ConstraintSystem<F: IsField> {
    num_variables: usize,
    constraints: Vec<PlonkConstraint<F>>,
}

#[allow(unused)]
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

    fn null_variable(&self) -> Variable {
        0
    }

    fn new_variable(&mut self) -> Variable {
        let variable_id = self.num_variables;
        self.num_variables += 1;
        variable_id
    }

    fn add_constraint(&mut self, constraint: PlonkConstraint<F>) {
        self.constraints.push(constraint);
    }

    /// Generates a new variable `v = c1 * v1 + c2 * v2 + b`
    fn linear_combination(
        &mut self,
        v1: &Variable,
        c1: FieldElement<F>,
        v2: &Variable,
        c2: FieldElement<F>,
        b: FieldElement<F>,
        hint: Option<Hint<F>>,
    ) -> Variable {
        let result = self.new_variable();
        self.add_constraint(PlonkConstraint {
            constraint_type: ConstraintType {
                ql: c1,
                qr: c2,
                qm: FieldElement::zero(),
                qo: -FieldElement::one(),
                qc: b,
            },
            l: *v1,
            r: *v2,
            o: result,
            hint,
        });
        result
    }

    /// Generates a new variables `w = c * v + b`
    fn linear_function(
        &mut self,
        v: &Variable,
        c: FieldElement<F>,
        b: FieldElement<F>,
        hint: Option<Hint<F>>,
    ) -> Variable {
        let result = self.new_variable();
        self.add_constraint(PlonkConstraint {
            constraint_type: ConstraintType {
                ql: c,
                qr: FieldElement::zero(),
                qm: FieldElement::zero(),
                qo: -FieldElement::one(),
                qc: b,
            },
            l: *v,
            r: self.null_variable(),
            o: result,
            hint,
        });
        result
    }

    fn add(&mut self, v1: &Variable, v2: &Variable) -> Variable {
        self.linear_combination(
            v1,
            FieldElement::one(),
            v2,
            FieldElement::one(),
            FieldElement::zero(),
            None,
        )
    }

    fn add_constant(&mut self, v: &Variable, constant: FieldElement<F>) -> Variable {
        self.linear_function(v, FieldElement::one(), constant, None)
    }

    fn mul(&mut self, v1: &Variable, v2: &Variable) -> Variable {
        let result = self.new_variable();
        self.add_constraint(PlonkConstraint {
            constraint_type: ConstraintType {
                ql: FieldElement::zero(),
                qr: FieldElement::zero(),
                qm: FieldElement::one(),
                qo: -FieldElement::one(),
                qc: FieldElement::zero(),
            },
            l: *v1,
            r: *v2,
            o: result,
            hint: None,
        });
        result
    }

    // TODO: check 0.div(0) does not compile
    fn div(&mut self, v1: &Variable, v2: &Variable) -> Variable {
        let result = self.new_variable();
        self.add_constraint(PlonkConstraint {
            constraint_type: ConstraintType {
                ql: FieldElement::zero(),
                qr: FieldElement::zero(),
                qm: FieldElement::one(),
                qo: -FieldElement::one(),
                qc: FieldElement::zero(),
            },
            l: result,
            r: *v2,
            o: *v1,
            hint: None,
        });
        result
    }

    fn new_boolean(&mut self) -> Variable {
        let boolean = self.new_variable();
        self.add_constraint(PlonkConstraint {
            constraint_type: ConstraintType {
                ql: -FieldElement::one(),
                qr: FieldElement::zero(),
                qm: FieldElement::one(),
                qo: FieldElement::zero(),
                qc: FieldElement::zero(),
            },
            l: boolean,
            r: boolean,
            o: self.null_variable(),
            hint: None,
        });
        boolean
    }

    fn new_u32(&mut self, v: &Variable) -> Vec<Variable>
    where
        F: IsPrimeField,
    {
        let bits: Vec<_> = (0..32).map(|_| self.new_boolean()).collect();
        let mut aux_vars: Vec<Variable> = Vec::new();
        let hint_function = |v: &FieldElement<F>| {
            if v.representative() & 1.into() == 1.into() {
                FieldElement::one()
            } else {
                FieldElement::zero()
            }
        };

        let hint = Some(Hint {
            function: hint_function,
            input: Column::O,
            output: Column::R,
        });
        // t0 := 2 b_0 + b_1
        let t_0 = self.linear_combination(
            &bits[0],
            FieldElement::from(2),
            &bits[1],
            FieldElement::one(),
            FieldElement::zero(),
            hint.clone(),
        );
        aux_vars.push(t_0);
        for bit in bits.iter().take(32).skip(2) {
            // t_{i+1} := 2 t_i + b_i
            let t_i = self.linear_combination(
                aux_vars.last().unwrap(),
                FieldElement::from(2),
                bit,
                FieldElement::one(),
                FieldElement::zero(),
                hint.clone(),
            );
            aux_vars.push(t_i);
        }
        self.assert_eq(v, aux_vars.last().unwrap());
        bits
    }

    fn not(&mut self, v: &Variable) -> Variable {
        let result = self.new_variable();
        self.add_constraint(PlonkConstraint {
            constraint_type: ConstraintType {
                ql: FieldElement::one(),
                qr: FieldElement::one(),
                qm: FieldElement::zero(),
                qo: FieldElement::zero(),
                qc: -FieldElement::one(),
            },
            l: *v,
            r: result,
            o: self.null_variable(),
            hint: None,
        });
        result
    }

    fn inv(&mut self, v: &Variable) -> (Variable, Variable) {
        let is_zero = self.new_variable();
        let v_inverse = self.new_variable();
        let hint = Some(Hint {
            function: |v: &FieldElement<F>| {
                if *v == FieldElement::zero() {
                    FieldElement::one()
                } else {
                    FieldElement::zero()
                }
            },
            input: Column::L,
            output: Column::R,
        });
        // v * z == 0
        self.add_constraint(PlonkConstraint {
            constraint_type: ConstraintType {
                ql: FieldElement::zero(),
                qr: FieldElement::zero(),
                qm: FieldElement::one(),
                qo: FieldElement::zero(),
                qc: FieldElement::zero(),
            },
            l: *v,
            r: is_zero,
            o: self.null_variable(),
            hint,
        });
        // v * w + z == 1
        self.add_constraint(PlonkConstraint {
            constraint_type: ConstraintType {
                ql: FieldElement::zero(),
                qr: FieldElement::zero(),
                qm: FieldElement::one(),
                qo: FieldElement::one(),
                qc: -FieldElement::one(),
            },
            l: *v,
            r: v_inverse, // w
            o: is_zero,   // z
            hint: Some(Hint {
                function: |v: &FieldElement<F>| {
                    if *v == FieldElement::zero() {
                        FieldElement::zero()
                    } else {
                        v.inv()
                    }
                },
                input: Column::L,
                output: Column::R,
            }),
        });
        (is_zero, v_inverse)
    }

    fn assert_eq(&mut self, v1: &Variable, v2: &Variable) {
        self.add_constraint(PlonkConstraint {
            constraint_type: ConstraintType {
                ql: FieldElement::one(),
                qr: -FieldElement::one(),
                qm: FieldElement::zero(),
                qo: FieldElement::zero(),
                qc: FieldElement::zero(),
            },
            l: *v1,
            r: *v2,
            o: self.null_variable(),
            hint: None,
        });
    }

    fn if_else(&mut self, boolean_condition: &Variable, v1: &Variable, v2: &Variable) -> Variable {
        let not_boolean_condition = self.not(boolean_condition);
        let if_branch = self.mul(v1, boolean_condition);
        let else_branch = self.mul(v2, &not_boolean_condition);
        self.add(&if_branch, &else_branch)
    }

    fn if_nonzero_else(&mut self, condition: &Variable, v1: &Variable, v2: &Variable) -> Variable {
        let (is_zero, _) = self.inv(condition);
        self.if_else(&is_zero, v2, v1)
    }

    fn solve(&self, assignments: &mut HashMap<Variable, FieldElement<F>>) -> Result<(), ()> {
        let mut number_solved = 0;
        let mut checked_constraints = vec![false; self.constraints.len()];
        loop {
            let old_solved = number_solved;
            for (i, constraint) in self.constraints.iter().enumerate() {
                let ct = &constraint.constraint_type;
                let has_l = assignments.contains_key(&constraint.l);
                let has_r = assignments.contains_key(&constraint.r);
                let has_o = assignments.contains_key(&constraint.o);

                if let Some(hint) = &constraint.hint {
                    let function = hint.function;
                    match (&hint.input, &hint.output, has_l, has_r, has_o) {
                        (Column::L, Column::R, true, false, _) => {
                            assignments.insert(
                                constraint.r,
                                function(assignments.get(&constraint.l).unwrap()),
                            );
                            number_solved += 1;
                        }
                        (Column::L, Column::O, true, _, false) => {
                            assignments.insert(
                                constraint.o,
                                function(assignments.get(&constraint.l).unwrap()),
                            );
                            number_solved += 1;
                        }
                        (Column::R, Column::L, false, true, _) => {
                            assignments.insert(
                                constraint.l,
                                function(assignments.get(&constraint.r).unwrap()),
                            );
                            number_solved += 1;
                        }
                        (Column::R, Column::O, _, true, false) => {
                            assignments.insert(
                                constraint.o,
                                function(assignments.get(&constraint.r).unwrap()),
                            );
                            number_solved += 1;
                        }
                        (Column::O, Column::L, false, _, true) => {
                            assignments.insert(
                                constraint.l,
                                function(assignments.get(&constraint.o).unwrap()),
                            );
                            number_solved += 1;
                        }
                        (Column::O, Column::R, _, false, true) => {
                            assignments.insert(
                                constraint.r,
                                function(assignments.get(&constraint.o).unwrap()),
                            );
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
                number_solved += 1;
            }
            if number_solved == old_solved {
                break;
            }
        }
        for (constraint, checked) in self.constraints.iter().zip(checked_constraints.iter()) {
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
}

#[cfg(test)]
mod tests {
    use super::*;
    use lambdaworks_math::field::{element::FieldElement, fields::u64_prime_field::U64PrimeField};
    #[test]
    fn test_linear_combination() {
        let system = &mut ConstraintSystem::<U64PrimeField<65537>>::new();

        let v1 = system.new_variable();
        let c1 = FieldElement::from(15);
        let v2 = system.new_variable();
        let c2 = -FieldElement::from(7);
        let b = FieldElement::from(99);
        let result = system.linear_combination(&v1, c1, &v2, c2, b, None);

        let x = FieldElement::from(17);
        let y = FieldElement::from(29);

        let mut inputs = HashMap::from([(v1, x), (v2, y)]);

        system.solve(&mut inputs).unwrap();
        assert_eq!(inputs.get(&result).unwrap(), &(x * c1 + y * c2 + b));
    }

    #[test]
    fn test_linear_function() {
        let system = &mut ConstraintSystem::<U64PrimeField<65537>>::new();

        let v = system.new_variable();
        let c = FieldElement::from(8);
        let b = FieldElement::from(109);
        let result = system.linear_function(&v, c, b, None);

        let x = FieldElement::from(17);

        let mut inputs = HashMap::from([(v, x)]);

        system.solve(&mut inputs).unwrap();
        assert_eq!(inputs.get(&result).unwrap(), &(x * c + b));
    }

    #[test]
    fn test_add() {
        let system = &mut ConstraintSystem::<U64PrimeField<65537>>::new();

        let input1 = system.new_variable();
        let input2 = system.new_variable();
        let result = system.add(&input1, &input2);

        let a = FieldElement::from(3);
        let b = FieldElement::from(10);

        let mut inputs = HashMap::from([(input1, a), (input2, b)]);

        system.solve(&mut inputs).unwrap();
        assert_eq!(inputs.get(&result).unwrap(), &(a + b));
    }

    #[test]
    fn test_mul() {
        let system = &mut ConstraintSystem::<U64PrimeField<65537>>::new();

        let input1 = system.new_variable();
        let input2 = system.new_variable();
        let result = system.mul(&input1, &input2);

        let a = FieldElement::from(3);
        let b = FieldElement::from(11);

        let mut inputs = HashMap::from([(input1, a), (input2, b)]);

        system.solve(&mut inputs).unwrap();
        assert_eq!(inputs.get(&result).unwrap(), &(a * b));
    }

    #[test]
    fn test_div() {
        let system = &mut ConstraintSystem::<U64PrimeField<65537>>::new();

        let input1 = system.new_variable();
        let input2 = system.new_variable();
        let result = system.div(&input1, &input2);

        let a = FieldElement::from(3);
        let b = FieldElement::from(11);

        let mut inputs = HashMap::from([(input1, a), (input2, b)]);

        system.solve(&mut inputs).unwrap();
        assert_eq!(inputs.get(&result).unwrap(), &(a / b));
    }

    #[test]
    fn test_add_constant() {
        let system = &mut ConstraintSystem::<U64PrimeField<65537>>::new();

        let input1 = system.new_variable();
        let b = FieldElement::from(11);
        let result = system.add_constant(&input1, b.clone());

        let a = FieldElement::from(3);

        let mut inputs = HashMap::from([(input1, FieldElement::from(a))]);

        system.solve(&mut inputs).unwrap();
        assert_eq!(inputs.get(&result).unwrap(), &(a + b));
    }

    #[test]
    fn test_not() {
        let system = &mut ConstraintSystem::<U64PrimeField<65537>>::new();

        let boolean = system.new_boolean();
        let result1 = system.not(&boolean);
        let result2 = system.not(&result1);

        let mut inputs = HashMap::from([(boolean, FieldElement::one())]);

        system.solve(&mut inputs).unwrap();
        assert_eq!(inputs.get(&result1).unwrap(), &FieldElement::zero());
        assert_eq!(inputs.get(&result2).unwrap(), &FieldElement::one());
    }

    #[test]
    fn test_inv() {
        let system = &mut ConstraintSystem::<U64PrimeField<65537>>::new();

        let v = system.new_variable();
        let w = system.new_variable();
        let (v_is_zero, v_inverse) = system.inv(&v);
        let (w_is_zero, w_inverse) = system.inv(&w);

        let mut inputs = HashMap::from([(v, FieldElement::from(2)), (w, FieldElement::from(0))]);

        system.solve(&mut inputs).unwrap();
        assert_eq!(
            inputs.get(&v_inverse).unwrap(),
            &FieldElement::from(2).inv()
        );
        assert_eq!(inputs.get(&v_is_zero).unwrap(), &FieldElement::zero());
        assert_eq!(inputs.get(&w_inverse).unwrap(), &FieldElement::from(0));
        assert_eq!(inputs.get(&w_is_zero).unwrap(), &FieldElement::one());
    }

    #[test]
    fn test_assert_eq_1() {
        let system = &mut ConstraintSystem::<U64PrimeField<65537>>::new();

        let v = system.new_variable();
        let w = system.new_variable();
        let z = system.mul(&v, &w);
        let output = system.new_variable();
        system.assert_eq(&z, &output);

        let mut inputs = HashMap::from([
            (v, FieldElement::from(2)),
            (w, FieldElement::from(2).inv()),
            (output, FieldElement::from(1)),
        ]);

        system.solve(&mut inputs).unwrap();
    }

    #[test]
    fn test_assert_eq_2() {
        let system = &mut ConstraintSystem::<U64PrimeField<65537>>::new();

        let v = system.new_variable();
        let w = system.new_variable();
        let z = system.mul(&v, &w);
        let output = system.new_variable();
        system.assert_eq(&z, &output);

        let mut inputs = HashMap::from([
            (v, FieldElement::from(2)),
            (w, FieldElement::from(2)),
            (output, FieldElement::from(1)),
        ]);

        system.solve(&mut inputs).unwrap_err();
    }

    #[test]
    fn test_if_nonzero_else_1() {
        let system = &mut ConstraintSystem::<U64PrimeField<65537>>::new();

        let v = system.new_variable();
        let v2 = system.mul(&v, &v);
        let v4 = system.mul(&v2, &v2);
        let w = system.add_constant(&v4, -FieldElement::one());
        let output = system.if_nonzero_else(&w, &v, &v2);

        let mut inputs = HashMap::from([(v, FieldElement::from(256))]);

        system.solve(&mut inputs).unwrap();
        assert_eq!(inputs.get(&output).unwrap(), inputs.get(&v2).unwrap());
    }

    #[test]
    fn test_if_nonzero_else_2() {
        let system = &mut ConstraintSystem::<U64PrimeField<65537>>::new();

        let v = system.new_variable();
        let v2 = system.mul(&v, &v);
        let v4 = system.mul(&v2, &v2);
        let w = system.add_constant(&v4, -FieldElement::one());
        let output = system.if_nonzero_else(&w, &v, &v2);

        let mut inputs = HashMap::from([(v, FieldElement::from(255))]);

        system.solve(&mut inputs).unwrap();
        assert_eq!(inputs.get(&output).unwrap(), inputs.get(&v).unwrap());
    }

    #[test]
    fn test_u32() {
        let system = &mut ConstraintSystem::<U64PrimeField<17>>::new();

        let input = system.new_variable();
        let u32_var = system.new_u32(&input);

        let input_assignment = 13;
        let mut inputs = HashMap::from([(input, FieldElement::from(input_assignment))]);

        system.solve(&mut inputs).unwrap();

        for i in 0..32 {
            assert_eq!(
                inputs.get(&u32_var[i]).unwrap().representative(),
                (input_assignment >> (31 - i)) & 1
            );
        }
    }

    #[test]
    fn test_pow() {
        let system = &mut ConstraintSystem::<U64PrimeField<65537>>::new();

        let base = system.new_variable();
        let exponent = system.new_variable();
        let exponent_bits = system.new_u32(&exponent);
        let mut result = system.new_variable();
        let result_first_value = result;

        assert_eq!(exponent_bits.len(), 32);
        for i in 0..32 {
            if i != 0 {
                result = system.mul(&result, &result);
            }
            let result_times_base = system.mul(&result, &base);
            result = system.if_else(&exponent_bits[i], &result_times_base, &result);
        }
        let mut inputs = HashMap::from([
            (base, FieldElement::from(3)),
            (exponent, FieldElement::from(10)),
            (result_first_value, FieldElement::from(1)),
        ]);

        system.solve(&mut inputs).unwrap();
        assert_eq!(inputs.get(&result).unwrap(), &FieldElement::from(59049));
    }
}
