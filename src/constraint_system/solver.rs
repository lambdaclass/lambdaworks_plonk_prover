use std::collections::HashMap;

use lambdaworks_math::field::{element::FieldElement as FE, traits::IsField};

use super::{Column, ConstraintSystem, Variable};

/// Finds a solution of the system that extends the `assignments` map.
/// If there is no such extension, it returns an error.
#[allow(unused)]
impl<F> ConstraintSystem<F>
where
    F: IsField,
{
    pub fn solve(
        &self,
        mut assignments: HashMap<Variable, FE<F>>,
    ) -> Result<(HashMap<Variable, FE<F>>), ()> {
        let mut number_solved = 0;
        let mut checked_constraints = vec![false; self.constraints.len()];
        loop {
            let old_solved = number_solved;
            for (i, constraint) in self.constraints.iter().enumerate() {
                let ct = &constraint.constraint_type;
                let mut has_l = assignments.contains_key(&constraint.l);
                let mut has_r = assignments.contains_key(&constraint.r);
                let mut has_o = assignments.contains_key(&constraint.o);

                if let Some(hint) = &constraint.hint {
                    let function = hint.function;
                    match (&hint.input, &hint.output, has_l, has_r, has_o) {
                        (Column::L, Column::R, true, false, _) => {
                            assignments.insert(
                                constraint.r,
                                function(assignments.get(&constraint.l).unwrap()),
                            );
                            number_solved += 1;
                            has_r = true;
                        }
                        (Column::L, Column::O, true, _, false) => {
                            assignments.insert(
                                constraint.o,
                                function(assignments.get(&constraint.l).unwrap()),
                            );
                            has_o = true;
                            number_solved += 1;
                        }
                        (Column::R, Column::L, false, true, _) => {
                            assignments.insert(
                                constraint.l,
                                function(assignments.get(&constraint.r).unwrap()),
                            );
                            has_l = true;
                            number_solved += 1;
                        }
                        (Column::R, Column::O, _, true, false) => {
                            assignments.insert(
                                constraint.o,
                                function(assignments.get(&constraint.r).unwrap()),
                            );
                            has_o = true;
                            number_solved += 1;
                        }
                        (Column::O, Column::L, false, _, true) => {
                            assignments.insert(
                                constraint.l,
                                function(assignments.get(&constraint.o).unwrap()),
                            );
                            has_l = true;
                            number_solved += 1;
                        }
                        (Column::O, Column::R, _, false, true) => {
                            assignments.insert(
                                constraint.r,
                                function(assignments.get(&constraint.o).unwrap()),
                            );
                            has_r = true;
                            number_solved += 1;
                        }
                        _ => {}
                    }
                }

                // a Ql + b Qr + a b Qm + c Qo + Qc = 0
                if has_l && has_r && has_o {
                    continue;
                } else if has_l && has_r && !has_o {
                    let a = assignments.get(&constraint.l).unwrap();
                    let b = assignments.get(&constraint.r).unwrap();
                    if ct.qo != FE::zero() {
                        let mut c = a * &ct.ql + b * &ct.qr + a * b * &ct.qm + &ct.qc;
                        c = -c * ct.qo.inv();
                        assignments.insert(constraint.o, c);
                    } else {
                        continue;
                    }
                } else if has_l && !has_r && has_o {
                    let a = assignments.get(&constraint.l).unwrap();
                    let c = assignments.get(&constraint.o).unwrap();
                    let denominator = &ct.qr + a * &ct.qm;
                    if denominator != FE::zero() {
                        let mut b = a * &ct.ql + c * &ct.qo + &ct.qc;
                        b = -b * denominator.inv();
                        assignments.insert(constraint.r, b);
                    } else {
                        continue;
                    }
                } else if !has_l && has_r && has_o {
                    let b = assignments.get(&constraint.r).unwrap();
                    let c = assignments.get(&constraint.o).unwrap();
                    let denominator = &ct.ql + b * &ct.qm;
                    if denominator != FE::zero() {
                        let mut a = b * &ct.qr + c * &ct.qo + &ct.qc;
                        a = -a * denominator.inv();
                        assignments.insert(constraint.l, a);
                    } else {
                        continue;
                    }
                } else if has_l && !has_r && !has_o {
                    let a = assignments.get(&constraint.l).unwrap();
                    let b_coefficient = &ct.qr + a * &ct.qm;
                    if b_coefficient == FE::zero() && ct.qo != FE::zero() {
                        let c = -(a * &ct.ql + &ct.qc) * ct.qo.inv();
                        assignments.insert(constraint.o, c);
                    } else if b_coefficient != FE::zero() && ct.qo == FE::zero() {
                        let b = -(a * &ct.ql + &ct.qc) * b_coefficient.inv();
                        assignments.insert(constraint.r, b);
                    } else {
                        continue;
                    }
                } else if !has_l && has_r && !has_o {
                    let b = assignments.get(&constraint.r).unwrap();
                    let a_coefficient = &ct.ql + b * &ct.qm;
                    if a_coefficient == FE::zero() && ct.qo != FE::zero() {
                        let c = -(b * &ct.qr + &ct.qc) * ct.qo.inv();
                        assignments.insert(constraint.o, c);
                    } else if a_coefficient != FE::zero() && ct.qo == FE::zero() {
                        let a = -(b * &ct.qr + &ct.qc) * a_coefficient.inv();
                        assignments.insert(constraint.l, a);
                    } else {
                        continue;
                    }
                } else if !has_l && !has_r && has_o && ct.qo != FE::zero() {
                    let c = assignments.get(&constraint.o).unwrap();
                    if ct.ql != FE::zero() && ct.qr == FE::zero() {
                        let a = -(c * &ct.qo + &ct.qc) * ct.ql.inv();
                        assignments.insert(constraint.l, a);
                    } else if ct.ql == FE::zero() && ct.qr != FE::zero() {
                        let b = -(c * &ct.qo + &ct.qc) * ct.qr.inv();
                        assignments.insert(constraint.r, b);
                    } else {
                        continue;
                    }
                } else if !has_l
                    && !has_r
                    && !has_o
                    && ct.ql != FE::zero()
                    && ct.qr == FE::zero()
                    && ct.qm == FE::zero()
                    && ct.qo == FE::zero()
                {
                    let a = -&ct.qc * ct.ql.inv();
                    assignments.insert(constraint.l, a);
                } else if !has_l
                    && !has_r
                    && !has_o
                    && ct.ql == FE::zero()
                    && ct.qr != FE::zero()
                    && ct.qm == FE::zero()
                    && ct.qo == FE::zero()
                {
                    let b = -&ct.qc * ct.qr.inv();
                    assignments.insert(constraint.r, b);
                } else if !has_l
                    && !has_r
                    && !has_o
                    && ct.ql == FE::zero()
                    && ct.qr == FE::zero()
                    && ct.qm == FE::zero()
                    && ct.qo != FE::zero()
                {
                    let c = -&ct.qc * ct.qo.inv();
                    assignments.insert(constraint.o, c);
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
                        if result != FE::zero() {
                            return Err(());
                        }
                    }
                    _ => return Err(()),
                }
            }
        }
        Ok(assignments)
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use crate::constraint_system::{Constraint, ConstraintSystem, ConstraintType};
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
}
