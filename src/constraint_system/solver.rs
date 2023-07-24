use std::collections::HashMap;

use lambdaworks_math::field::{element::FieldElement as FE, traits::IsField};

use super::{errors::SolverError, Column, Constraint, ConstraintSystem, Variable};

/// Finds a solution to the system extending the `assignments` map.
/// It returns an error in case there is no such solution.
#[allow(unused)]
impl<F> ConstraintSystem<F>
where
    F: IsField,
{
    pub fn solve(
        &self,
        mut assignments: HashMap<Variable, FE<F>>,
    ) -> Result<(HashMap<Variable, FE<F>>), SolverError> {
        let mut num_solved = 0;
        loop {
            let old_solved = num_solved;
            for constraint in self.constraints.iter() {
                (assignments, num_solved) = solve_hint(assignments, constraint, num_solved);
                (assignments, num_solved) = solve_constraint(assignments, constraint, num_solved);
            }
            if num_solved == old_solved {
                break;
            }
        }

        // Check the system is solved
        for constraint in self.constraints.iter() {
            let a = assignments.get(&constraint.l);
            let b = assignments.get(&constraint.r);
            let c = assignments.get(&constraint.o);

            match (a, b, c) {
                (Some(a), Some(b), Some(c)) => {
                    let ct = &constraint.constraint_type;
                    let result = a * &ct.ql + b * &ct.qr + a * b * &ct.qm + c * &ct.qo + &ct.qc;
                    if result != FE::zero() {
                        return Err(SolverError::InconsistentSystem);
                    }
                }
                _ => return Err(SolverError::IndeterminateSystem),
            }
        }
        Ok(assignments)
    }
}

fn solve_hint<F: IsField>(
    mut assignments: HashMap<Variable, FE<F>>,
    constraint: &Constraint<F>,
    mut number_solved: usize,
) -> (HashMap<Variable, FE<F>>, usize) {
    let column_to_variable = |column: &Column| match column {
        Column::L => constraint.l,
        Column::R => constraint.r,
        Column::O => constraint.o,
    };
    if let Some(hint) = &constraint.hint {
        if !assignments.contains_key(&column_to_variable(&hint.output)) {
            if let Some(input) = assignments.get(&column_to_variable(&hint.input)) {
                assignments.insert(column_to_variable(&hint.output), (hint.function)(input));
                number_solved += 1;
            }
        }
    }

    (assignments, number_solved)
}

fn solve_constraint<F: IsField>(
    mut assignments: HashMap<Variable, FE<F>>,
    constraint: &Constraint<F>,
    number_solved: usize,
) -> (HashMap<Variable, FE<F>>, usize) {
    let ct = &constraint.constraint_type;
    let a = assignments.get(&constraint.l);
    let b = assignments.get(&constraint.r);
    let c = assignments.get(&constraint.o);
    let zero = FE::zero();

    match (
        (a, b, c),
        (ct.ql == zero, ct.qr == zero, ct.qm == zero, ct.qo == zero),
    ) {
        ((Some(a), Some(b), None), _) => {
            if ct.qo != FE::zero() {
                let mut c = a * &ct.ql + b * &ct.qr + a * b * &ct.qm + &ct.qc;
                c = -c * ct.qo.inv();
                assignments.insert(constraint.o, c);
            } else {
                return (assignments, number_solved);
            }
        }
        ((Some(a), None, Some(c)), _) => {
            let denominator = &ct.qr + a * &ct.qm;
            if denominator != FE::zero() {
                let mut b = a * &ct.ql + c * &ct.qo + &ct.qc;
                b = -b * denominator.inv();
                assignments.insert(constraint.r, b);
            } else {
                return (assignments, number_solved);
            }
        }
        ((None, Some(b), Some(c)), _) => {
            let denominator = &ct.ql + b * &ct.qm;
            if denominator != FE::zero() {
                let mut a = b * &ct.qr + c * &ct.qo + &ct.qc;
                a = -a * denominator.inv();
                assignments.insert(constraint.l, a);
            } else {
                return (assignments, number_solved);
            }
        }
        ((Some(a), None, None), _) => {
            let b_coefficient = &ct.qr + a * &ct.qm;
            if b_coefficient == FE::zero() && ct.qo != FE::zero() {
                let c = -(a * &ct.ql + &ct.qc) * ct.qo.inv();
                assignments.insert(constraint.o, c);
            } else if b_coefficient != FE::zero() && ct.qo == FE::zero() {
                let b = -(a * &ct.ql + &ct.qc) * b_coefficient.inv();
                assignments.insert(constraint.r, b);
            } else {
                return (assignments, number_solved);
            }
        }
        ((None, Some(b), None), _) => {
            let a_coefficient = &ct.ql + b * &ct.qm;
            if a_coefficient == FE::zero() && ct.qo != FE::zero() {
                let c = -(b * &ct.qr + &ct.qc) * ct.qo.inv();
                assignments.insert(constraint.o, c);
            } else if a_coefficient != FE::zero() && ct.qo == FE::zero() {
                let a = -(b * &ct.qr + &ct.qc) * a_coefficient.inv();
                assignments.insert(constraint.l, a);
            } else {
                return (assignments, number_solved);
            }
        }
        ((None, None, Some(c)), (false, true, true, _)) => {
            let a = -(c * &ct.qo + &ct.qc) * ct.ql.inv();
            assignments.insert(constraint.l, a);
        }
        ((None, None, Some(c)), (true, false, true, _)) => {
            let b = -(c * &ct.qo + &ct.qc) * ct.qr.inv();
            assignments.insert(constraint.r, b);
        }
        ((None, None, None), (true, true, true, false)) => {
            let c = -&ct.qc * ct.qo.inv();
            assignments.insert(constraint.o, c);
        }
        ((None, None, None), (true, false, true, true)) => {
            let b = -&ct.qc * ct.qr.inv();
            assignments.insert(constraint.r, b);
        }
        ((None, None, None), (false, true, true, true)) => {
            let a = -&ct.qc * ct.ql.inv();
            assignments.insert(constraint.l, a);
        }
        _ => {
            return (assignments, number_solved);
        }
    }
    (assignments, number_solved + 1)
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use crate::constraint_system::{
        errors::SolverError, Constraint, ConstraintSystem, ConstraintType,
    };
    use lambdaworks_math::field::{
        element::FieldElement as FE, fields::u64_prime_field::U64PrimeField,
    };

    #[test]
    // All values are known
    fn test_case_all_values_are_known() {
        let mut system = ConstraintSystem::<U64PrimeField<65537>>::new();
        let a = system.new_variable();
        let b = system.new_variable();
        let c = system.new_variable();
        let constraint = Constraint {
            constraint_type: ConstraintType {
                ql: FE::one(),
                qr: FE::one(),
                qm: FE::one(),
                qo: -FE::one(),
                qc: FE::one(),
            },
            hint: None,
            l: a,
            r: b,
            o: c,
        };
        system.add_constraint(constraint);
        let inputs = HashMap::from([(a, FE::from(2)), (b, FE::from(3)), (c, FE::from(12))]);
        system.solve(inputs).unwrap();
    }

    #[test]
    // `b` and `c` are known.
    fn test_case_b_and_c_are_known() {
        let mut system = ConstraintSystem::<U64PrimeField<65537>>::new();
        let a = system.new_variable();
        let b = system.new_variable();
        let c = system.new_variable();
        let constraint = Constraint {
            constraint_type: ConstraintType {
                ql: FE::one(),
                qr: FE::one(),
                qm: FE::one(),
                qo: -FE::one(),
                qc: FE::one(),
            },
            hint: None,
            l: a,
            r: b,
            o: c,
        };
        system.add_constraint(constraint);
        let inputs = HashMap::from([(b, FE::from(3)), (c, FE::from(12))]);
        let assignments = system.solve(inputs).unwrap();
        assert_eq!(assignments.get(&a).unwrap(), &FE::from(2));
    }

    #[test]
    // `a` and `c` are known.
    fn test_case_a_and_c_are_known() {
        let mut system = ConstraintSystem::<U64PrimeField<65537>>::new();
        let a = system.new_variable();
        let b = system.new_variable();
        let c = system.new_variable();
        let constraint = Constraint {
            constraint_type: ConstraintType {
                ql: FE::one(),
                qr: FE::one(),
                qm: FE::one(),
                qo: -FE::one(),
                qc: FE::one(),
            },
            hint: None,
            l: a,
            r: b,
            o: c,
        };
        system.add_constraint(constraint);
        let inputs = HashMap::from([(a, FE::from(2)), (c, FE::from(12))]);
        let assignments = system.solve(inputs).unwrap();
        assert_eq!(assignments.get(&b).unwrap(), &FE::from(3));
    }

    #[test]
    // `a` and `b` are known.
    fn test_case_a_and_b_are_known() {
        let mut system = ConstraintSystem::<U64PrimeField<65537>>::new();
        let a = system.new_variable();
        let b = system.new_variable();
        let c = system.new_variable();
        let constraint = Constraint {
            constraint_type: ConstraintType {
                ql: FE::one(),
                qr: FE::one(),
                qm: FE::one(),
                qo: -FE::one(),
                qc: FE::one(),
            },
            hint: None,
            l: a,
            r: b,
            o: c,
        };
        system.add_constraint(constraint);
        let inputs = HashMap::from([(a, FE::from(2)), (b, FE::from(3))]);
        let assignments = system.solve(inputs).unwrap();
        assert_eq!(assignments.get(&c).unwrap(), &FE::from(12));
    }

    #[test]
    // Only `a` is known and coefficient of `b` is zero in one constraint.
    fn test_case_only_a_is_known_but_bs_coeffient_is_zero() {
        let mut system = ConstraintSystem::<U64PrimeField<65537>>::new();
        let a = system.new_variable();
        let b = system.new_variable();
        let c = system.new_variable();
        let constraint1 = Constraint {
            constraint_type: ConstraintType {
                ql: FE::one(),
                qr: -FE::from(2),
                qm: FE::one(),
                qo: FE::one(),
                qc: FE::one(),
            },
            hint: None,
            l: a,
            r: b,
            o: c,
        };
        let constraint2 = Constraint {
            constraint_type: ConstraintType {
                ql: FE::one(),
                qr: FE::one(),
                qm: FE::zero(),
                qo: FE::zero(),
                qc: FE::zero(),
            },
            hint: None,
            l: b,
            r: c,
            o: system.null_variable(),
        };
        system.add_constraint(constraint1);
        system.add_constraint(constraint2);
        let inputs = HashMap::from([(a, FE::from(2))]);
        let assignments = system.solve(inputs).unwrap();
        assert_eq!(assignments.get(&b).unwrap(), &FE::from(3));
        assert_eq!(assignments.get(&c).unwrap(), &-FE::from(3));
    }

    #[test]
    // Only `a` is known and coefficient of `b` is not zero in one constraint.
    fn test_case_only_a_is_known_but_cs_coeffient_is_zero() {
        let mut system = ConstraintSystem::<U64PrimeField<65537>>::new();
        let a = system.new_variable();
        let b = system.new_variable();
        let c = system.new_variable();
        let constraint1 = Constraint {
            constraint_type: ConstraintType {
                ql: FE::one(),
                qr: FE::one(),
                qm: FE::one(),
                qo: FE::zero(),
                qc: -FE::from(5),
            },
            hint: None,
            l: a,
            r: b,
            o: c,
        };
        let constraint2 = Constraint {
            constraint_type: ConstraintType {
                ql: FE::one(),
                qr: FE::one(),
                qm: FE::zero(),
                qo: FE::zero(),
                qc: FE::zero(),
            },
            hint: None,
            l: b,
            r: c,
            o: system.null_variable(),
        };
        system.add_constraint(constraint1);
        system.add_constraint(constraint2);
        let inputs = HashMap::from([(a, FE::from(1))]);
        let assignments = system.solve(inputs).unwrap();
        assert_eq!(assignments.get(&b).unwrap(), &FE::from(2));
        assert_eq!(assignments.get(&c).unwrap(), &-FE::from(2));
    }

    #[test]
    // Only `b` is known and coefficient of `a` is zero in one constraint.
    fn test_case_only_b_is_known_but_as_coeffient_is_zero() {
        let mut system = ConstraintSystem::<U64PrimeField<65537>>::new();
        let a = system.new_variable();
        let b = system.new_variable();
        let c = system.new_variable();
        let constraint1 = Constraint {
            constraint_type: ConstraintType {
                ql: -FE::from(3),
                qr: FE::one(),
                qm: FE::one(),
                qo: FE::one(),
                qc: FE::one(),
            },
            hint: None,
            l: a,
            r: b,
            o: c,
        };
        let constraint2 = Constraint {
            constraint_type: ConstraintType {
                ql: FE::one(),
                qr: FE::one(),
                qm: FE::zero(),
                qo: FE::zero(),
                qc: FE::zero(),
            },
            hint: None,
            l: a,
            r: c,
            o: system.null_variable(),
        };
        system.add_constraint(constraint1);
        system.add_constraint(constraint2);
        let inputs = HashMap::from([(b, FE::from(3))]);
        let assignments = system.solve(inputs).unwrap();
        assert_eq!(assignments.get(&a).unwrap(), &FE::from(4));
        assert_eq!(assignments.get(&c).unwrap(), &-FE::from(4));
    }

    #[test]
    // Only `b` is known and coefficient of `a` is not zero in one constraint.
    fn test_case_only_b_is_known_but_cs_coeffient_is_zero() {
        let mut system = ConstraintSystem::<U64PrimeField<65537>>::new();
        let a = system.new_variable();
        let b = system.new_variable();
        let c = system.new_variable();
        let constraint1 = Constraint {
            constraint_type: ConstraintType {
                ql: FE::one(),
                qr: FE::one(),
                qm: FE::one(),
                qo: FE::zero(),
                qc: -FE::from(5),
            },
            hint: None,
            l: a,
            r: b,
            o: system.null_variable(),
        };
        let constraint2 = Constraint {
            constraint_type: ConstraintType {
                ql: FE::one(),
                qr: FE::one(),
                qm: FE::zero(),
                qo: FE::zero(),
                qc: FE::zero(),
            },
            hint: None,
            l: a,
            r: c,
            o: system.null_variable(),
        };
        system.add_constraint(constraint1);
        system.add_constraint(constraint2);
        let inputs = HashMap::from([(b, FE::from(1))]);
        let assignments = system.solve(inputs).unwrap();
        assert_eq!(assignments.get(&a).unwrap(), &FE::from(2));
        assert_eq!(assignments.get(&c).unwrap(), &-FE::from(2));
    }

    #[test]
    // Only `c` is known and coefficient of `b` is not zero in one constraint.
    fn test_case_only_c_is_known_but_bs_coeffient_is_zero() {
        let mut system = ConstraintSystem::<U64PrimeField<65537>>::new();
        let a = system.new_variable();
        let b = system.new_variable();
        let c = system.new_variable();
        let constraint1 = Constraint {
            constraint_type: ConstraintType {
                ql: FE::from(2),
                qr: FE::zero(),
                qm: FE::zero(),
                qo: FE::one(),
                qc: FE::zero(),
            },
            hint: None,
            l: a,
            r: b,
            o: c,
        };
        let constraint2 = Constraint {
            constraint_type: ConstraintType {
                ql: FE::one(),
                qr: FE::one(),
                qm: FE::zero(),
                qo: FE::zero(),
                qc: FE::zero(),
            },
            hint: None,
            l: a,
            r: b,
            o: system.null_variable(),
        };
        system.add_constraint(constraint1);
        system.add_constraint(constraint2);
        let inputs = HashMap::from([(c, FE::from(2))]);
        let assignments = system.solve(inputs).unwrap();
        assert_eq!(assignments.get(&a).unwrap(), &-FE::from(1));
        assert_eq!(assignments.get(&b).unwrap(), &FE::from(1));
    }

    #[test]
    // Only `c` is known and coefficient of `a` is not zero in one constraint.
    fn test_case_only_c_is_known_but_as_coeffient_is_zero() {
        let mut system = ConstraintSystem::<U64PrimeField<65537>>::new();
        let a = system.new_variable();
        let b = system.new_variable();
        let c = system.new_variable();
        let constraint1 = Constraint {
            constraint_type: ConstraintType {
                ql: FE::zero(),
                qr: FE::from(2),
                qm: FE::zero(),
                qo: FE::one(),
                qc: FE::zero(),
            },
            hint: None,
            l: a,
            r: b,
            o: c,
        };
        let constraint2 = Constraint {
            constraint_type: ConstraintType {
                ql: FE::one(),
                qr: FE::one(),
                qm: FE::zero(),
                qo: FE::zero(),
                qc: FE::zero(),
            },
            hint: None,
            l: a,
            r: b,
            o: system.null_variable(),
        };
        system.add_constraint(constraint1);
        system.add_constraint(constraint2);
        let inputs = HashMap::from([(c, FE::from(2))]);
        let assignments = system.solve(inputs).unwrap();
        assert_eq!(assignments.get(&a).unwrap(), &FE::from(1));
        assert_eq!(assignments.get(&b).unwrap(), &-FE::from(1));
    }

    #[test]
    fn test_case_all_values_are_unknown() {
        let mut system = ConstraintSystem::<U64PrimeField<65537>>::new();
        let a = system.new_variable();
        let b = system.new_variable();
        let c = system.new_variable();
        let constraint1 = Constraint {
            constraint_type: ConstraintType {
                ql: FE::from(2),
                qr: FE::zero(),
                qm: FE::zero(),
                qo: FE::zero(),
                qc: -FE::from(2),
            },
            hint: None,
            l: a,
            r: b,
            o: c,
        };
        let constraint2 = Constraint {
            constraint_type: ConstraintType {
                ql: FE::zero(),
                qr: FE::from(2),
                qm: FE::zero(),
                qo: FE::zero(),
                qc: -FE::from(4),
            },
            hint: None,
            l: a,
            r: b,
            o: c,
        };
        let constraint3 = Constraint {
            constraint_type: ConstraintType {
                ql: FE::zero(),
                qr: FE::zero(),
                qm: FE::zero(),
                qo: FE::from(2),
                qc: -FE::from(6),
            },
            hint: None,
            l: a,
            r: b,
            o: c,
        };
        system.add_constraint(constraint1);
        system.add_constraint(constraint2);
        system.add_constraint(constraint3);
        let inputs = HashMap::from([]);
        let assignments = system.solve(inputs).unwrap();
        assert_eq!(assignments.get(&a).unwrap(), &FE::from(1));
        assert_eq!(assignments.get(&b).unwrap(), &FE::from(2));
        assert_eq!(assignments.get(&c).unwrap(), &FE::from(3));
    }

    #[test]
    fn test_inconsistent_system() {
        let mut system = ConstraintSystem::<U64PrimeField<65537>>::new();
        let a = system.new_variable();
        let b = system.new_variable();
        let constraint1 = Constraint {
            constraint_type: ConstraintType {
                ql: FE::one(),
                qr: FE::one(),
                qm: FE::zero(),
                qo: FE::zero(),
                qc: FE::one(),
            },
            hint: None,
            l: a,
            r: b,
            o: system.null_variable(),
        };
        system.add_constraint(constraint1);
        let constraint2 = Constraint {
            constraint_type: ConstraintType {
                ql: -FE::one(),
                qr: FE::one(),
                qm: FE::zero(),
                qo: FE::zero(),
                qc: FE::one(),
            },
            hint: None,
            l: a,
            r: b,
            o: system.null_variable(),
        };
        let inputs = HashMap::from([(a, FE::from(2))]);
        system.add_constraint(constraint2);
        assert_eq!(
            system.solve(inputs).unwrap_err(),
            SolverError::InconsistentSystem
        );
    }

    #[test]
    fn test_indeterminate_system() {
        let mut system = ConstraintSystem::<U64PrimeField<65537>>::new();
        let a = system.new_variable();
        let b = system.new_variable();
        let constraint = Constraint {
            constraint_type: ConstraintType {
                ql: FE::one(),
                qr: FE::one(),
                qm: FE::zero(),
                qo: FE::zero(),
                qc: FE::one(),
            },
            hint: None,
            l: a,
            r: b,
            o: system.null_variable(),
        };
        let inputs = HashMap::from([]);
        system.add_constraint(constraint);
        assert_eq!(
            system.solve(inputs).unwrap_err(),
            SolverError::IndeterminateSystem
        );
    }
}
