use std::collections::HashMap;

use lambdaworks_math::field::{element::FieldElement as FE, traits::IsField};

use super::{Column, ConstraintSystem, Variable};

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
                } else if has_l && has_r {
                    let a = assignments.get(&constraint.l).unwrap();
                    let b = assignments.get(&constraint.r).unwrap();
                    let mut c = a * &ct.ql + b * &ct.qr + a * b * &ct.qm + &ct.qc;
                    if ct.qo == FE::zero() {
                        continue;
                    }
                    c = -c * ct.qo.inv();
                    assignments.insert(constraint.o, c);
                } else if has_l && has_o {
                    let a = assignments.get(&constraint.l).unwrap();
                    let c = assignments.get(&constraint.o).unwrap();
                    let mut b = a * &ct.ql + c * &ct.qo + &ct.qc;
                    let denominator = &ct.qr + a * &ct.qm;
                    if denominator == FE::zero() {
                        continue;
                    }
                    b = -b * denominator.inv();
                    assignments.insert(constraint.r, b);
                } else if has_r && has_o {
                    let b = assignments.get(&constraint.r).unwrap();
                    let c = assignments.get(&constraint.o).unwrap();
                    let mut a = b * &ct.qr + c * &ct.qo + &ct.qc;
                    let denominator = &ct.ql + b * &ct.qm;
                    if denominator == FE::zero() {
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
