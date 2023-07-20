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

#[derive(Clone)]
struct Hint<F: IsField> {
    function: fn(&FieldElement<F>) -> FieldElement<F>,
    input: Column,
    output: Column,
}

struct PlonkConstraint<F: IsField> {
    constraint_type: ConstraintType<F>,
    hint: Option<Hint<F>>, // func, input, output
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

    fn new_variable(&mut self) -> Variable {
        Variable(self.new_wire())
    }

    fn add_constraint(&mut self, constraint: PlonkConstraint<F>) {
        self.constraints.push(constraint);
    }

    /// Generates a new variables `v = c1 * v1 + c2 * v2 + b`
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
            l: v1.0,
            r: v2.0,
            o: result.0,
            hint: hint,
        });
        result
    }

    /// Generates a new variables `v = c1 * v1 + b`
    fn linear_function(
        &mut self,
        v: &Variable,
        c: FieldElement<F>,
        b: FieldElement<F>,
    ) -> Variable {
        let result = self.new_variable();
        self.add_constraint(PlonkConstraint {
            constraint_type: ConstraintType {
                ql: FieldElement::one(),
                qr: FieldElement::zero(),
                qm: FieldElement::zero(),
                qo: -FieldElement::one(),
                qc: b,
            },
            l: v.0,
            r: self.empty_wire(),
            o: result.0,
            hint: None,
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
        self.linear_function(v, FieldElement::one(), constant)
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
            l: v1.0,
            r: v2.0,
            o: result.0,
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
            l: result.0,
            r: v2.0,
            o: v1.0,
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
            l: boolean.0,
            r: boolean.0,
            o: self.empty_wire(),
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
        for i in 2..32 {
            // t_{i+1} := 2 t_i + b_i
            let t_i = self.linear_combination(
                &aux_vars.last().unwrap(),
                FieldElement::from(2),
                &bits[i],
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
            l: v.0,
            r: result.0,
            o: self.empty_wire(),
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
            l: v.0,
            r: is_zero.0,
            o: self.empty_wire(),
            hint: hint,
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
            l: v.0,
            r: v_inverse.0, // w
            o: is_zero.0,   // z
            hint: Some(Hint {
                function: |v: &FieldElement<F>| {
                    if *v == FieldElement::zero() {
                        FieldElement::one()
                    } else {
                        FieldElement::zero()
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
            l: v1.0,
            r: v2.0,
            o: self.empty_wire(),
            hint: None,
        });
    }

    fn if_else(&mut self, boolean_condition: &Variable, v1: &Variable, v2: &Variable) -> Variable {
        let not_boolean_condition = self.not(boolean_condition);
        let if_branch = self.mul(&v1, boolean_condition);
        let else_branch = self.mul(&v2, &not_boolean_condition);
        self.add(&if_branch, &else_branch)
    }

    fn if_neq_else(&mut self, condition: &Variable, v1: &Variable, v2: &Variable) -> Variable {
        let (is_zero, _) = self.inv(condition);
        self.if_else(&is_zero, v2, v1)
    }
}

struct Variable(usize);

impl Variable {
    fn new<F: IsField>(constraint_system: &mut ConstraintSystem<F>) -> Self {
        Variable(constraint_system.new_wire())
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
    #[test]
    fn test_add() {
        let system = &mut ConstraintSystem::<U64PrimeField<65537>>::new();

        let input1 = system.new_variable();
        let input2 = system.new_variable();
        let result = system.add(&input1, &input2);

        let a = 3;
        let b = 10;

        let mut inputs = HashMap::from([
            (input1.0, FieldElement::from(a)),
            (input2.0, FieldElement::from(b)),
        ]);

        solver(&system, &mut inputs).unwrap();
        assert_eq!(inputs.get(&result.0).unwrap(), &FieldElement::from(a + b));
    }

    #[test]
    fn test_mul() {
        let system = &mut ConstraintSystem::<U64PrimeField<65537>>::new();

        let input1 = system.new_variable();
        let input2 = system.new_variable();
        let result = system.mul(&input1, &input2);

        let a = 3;
        let b = 11;

        let mut inputs = HashMap::from([
            (input1.0, FieldElement::from(a)),
            (input2.0, FieldElement::from(b)),
        ]);

        solver(&system, &mut inputs).unwrap();
        assert_eq!(inputs.get(&result.0).unwrap(), &FieldElement::from(a * b));
    }

    #[test]
    fn test_div() {
        let system = &mut ConstraintSystem::<U64PrimeField<65537>>::new();

        let input1 = system.new_variable();
        let input2 = system.new_variable();
        let result = system.div(&input1, &input2);

        let a = FieldElement::from(3);
        let b = FieldElement::from(11);

        let mut inputs = HashMap::from([
            (input1.0, FieldElement::from(a)),
            (input2.0, FieldElement::from(b)),
        ]);

        solver(&system, &mut inputs).unwrap();
        assert_eq!(inputs.get(&result.0).unwrap(), &(a / b));
    }

    #[test]
    fn test_add_constant() {
        let system = &mut ConstraintSystem::<U64PrimeField<65537>>::new();

        let input1 = system.new_variable();
        let b = FieldElement::from(11);
        let result = system.add_constant(&input1, b.clone());

        let a = FieldElement::from(3);

        let mut inputs = HashMap::from([(input1.0, FieldElement::from(a))]);

        solver(&system, &mut inputs).unwrap();
        assert_eq!(inputs.get(&result.0).unwrap(), &(a + b));
    }

    // assert out == if(i1^2 + i1 * i2 + 5 != 0, i1, i2)
    #[test]
    fn test_constraint_system() {
        let system = &mut ConstraintSystem::<U64PrimeField<17>>::new();

        let input1 = system.new_variable();
        let input2 = system.new_variable();
        let output = system.new_variable();

        let z1 = system.add(&input1, &input2);
        let z2 = system.mul(&z1, &input1);
        let z3 = system.add_constant(&z2, FieldElement::from(5));
        let z4 = system.if_else(&z3, &input1, &input2);
        system.assert_eq(&z4, &output);

        println!("NUM WIRES: {}", system.num_variables);
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
        let system = &mut ConstraintSystem::<U64PrimeField<17>>::new();

        let input1 = system.new_variable();
        let input2 = system.new_variable();

        let z1 = system.add(&input1, &input2);
        let z2 = system.mul(&z1, &input1);
        system.add_constant(&z2, FieldElement::from(5));

        let mut inputs = HashMap::from([(0, FieldElement::one()), (1, FieldElement::from(2))]);

        solver(&system, &mut inputs).unwrap();

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
    fn test_solve_u32() {
        let system = &mut ConstraintSystem::<U64PrimeField<17>>::new();

        let input = system.new_variable();
        let u32_var = system.new_u32(&input);

        let input_assignment = 13;
        let mut inputs = HashMap::from([(0, FieldElement::from(input_assignment))]);

        solver(&system, &mut inputs).unwrap();

        for i in 0..32 {
            assert_eq!(
                inputs.get(&u32_var[i].0).unwrap().representative(),
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
        let result_first_value_id = result.0;

        assert_eq!(exponent_bits.len(), 32);
        for i in 0..32 {
            if i != 0 {
                result = system.mul(&result, &result);
            }
            let result_times_base = system.mul(&result, &base);
            result = system.if_else(&exponent_bits[i], &result_times_base, &result);
        }
        let mut inputs = HashMap::from([
            (base.0, FieldElement::from(3)),
            (exponent.0, FieldElement::from(10)),
            (result_first_value_id, FieldElement::from(1)),
        ]);

        solver(&system, &mut inputs).unwrap();
        assert_eq!(inputs.get(&result.0).unwrap(), &FieldElement::from(59049));
        println!("{:?}", system.num_variables);
    }
}
