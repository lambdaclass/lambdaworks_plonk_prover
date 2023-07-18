use core::fmt::Debug;
use std::collections::HashMap;
use lambdaworks_math::field::{element::FieldElement, traits::IsField};


// a Ql + b Qr + a b Qm + c Qo + Qc = 0
#[derive(Debug)]
struct ConstraintType<F: IsField> {
    l: FieldElement<F>,
    r: FieldElement<F>,
    m: FieldElement<F>,
    o: FieldElement<F>,
    c: FieldElement<F>,
}

// a Ql + b Qr + a b Qm + c Qo + Qc = 0
#[derive(Debug)]
struct PlonkConstraint<F: IsField> {
    constraint_type: ConstraintType<F>,
    a: usize,
    b: usize,
    c: usize,
}

#[derive(Debug)]
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

    fn new_variable(&mut self) -> usize {
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
        Variable(constraint_system.new_variable())
    }

    fn add<F: IsField>(&self, other: &Variable, constraint_system: &mut ConstraintSystem<F>) -> Self {
        let result = Self::new(constraint_system);
        constraint_system.add_constraint(PlonkConstraint {
            constraint_type: ConstraintType {
                l: FieldElement::one(),
                r: FieldElement::one(),
                m: FieldElement::zero(),
                o: -FieldElement::one(),
                c: FieldElement::zero(),
            },
            a: self.0,
            b: other.0,
            c: result.0,
        });
        result
    }

    fn mul<F: IsField>(&self, other: &Variable, constraint_system: &mut ConstraintSystem<F>) -> Self {
        let result = Self::new(constraint_system);
        constraint_system.add_constraint(PlonkConstraint {
            constraint_type: ConstraintType {
                l: FieldElement::zero(),
                r: FieldElement::zero(),
                m: FieldElement::one(),
                o: -FieldElement::one(),
                c: FieldElement::zero(),
            },
            a: self.0,
            b: other.0,
            c: result.0,
        });
        result
    }

    // TODO: check 0.div(0) does not compile
    fn div<F: IsField>(&self, other: &Self, constraint_system: &mut ConstraintSystem<F>) -> Self {
        let result = Self::new(constraint_system);
        constraint_system.add_constraint(PlonkConstraint {
            constraint_type: ConstraintType {
                l: FieldElement::zero(),
                r: FieldElement::zero(),
                m: FieldElement::one(),
                o: -FieldElement::one(),
                c: FieldElement::zero(),
            },
            a: result.0,
            b: other.0,
            c: self.0,
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
                l: FieldElement::one(),
                r: FieldElement::zero(),
                m: FieldElement::zero(),
                o: -FieldElement::one(),
                c: constant,
            },
            a: self.0,
            b: constraint_system.empty_wire(),
            c: result.0,
        });
        result
    }

    fn new_boolean<F: IsField>(constraint_system: &mut ConstraintSystem<F>) -> Self {
        let boolean = Self::new(constraint_system);
        constraint_system.add_constraint(PlonkConstraint {
            constraint_type: ConstraintType {
                l: -FieldElement::one(),
                r: FieldElement::zero(),
                m: FieldElement::one(),
                o: FieldElement::zero(),
                c: FieldElement::zero(),
            },
            a: boolean.0,
            b: boolean.0,
            c: constraint_system.empty_wire(),
        });
        boolean
    }

    fn not<F: IsField>(&self, constraint_system: &mut ConstraintSystem<F>) -> Self {
        let result = Self::new(constraint_system);
        constraint_system.add_constraint(PlonkConstraint {
            constraint_type: ConstraintType {
                l: FieldElement::one(),
                r: FieldElement::one(),
                m: FieldElement::zero(),
                o: FieldElement::zero(),
                c: -FieldElement::one(),
            },
            a: self.0,
            b: result.0,
            c: constraint_system.empty_wire(),
        });
        result
    }

    // Input: v, Genera: w, z
    // v * w + z = 1      - Si z es 0, entonces w es el inverso
    // v * z = 0          - Sólo v o z es 0
    fn inv<F: IsField>(v: &Self, constraint_system: &mut ConstraintSystem<F>) -> (Self, Self) {
        let is_zero = Self::new(constraint_system);
        let v_inverse = Self::new(constraint_system);
        constraint_system.add_constraint(PlonkConstraint {
            constraint_type: ConstraintType {
                l: FieldElement::zero(),
                r: FieldElement::zero(),
                m: FieldElement::one(),
                o: FieldElement::zero(),
                c: FieldElement::zero(),
            },
            a: v.0,
            b: is_zero.0,
            c: constraint_system.empty_wire(),
        });
        constraint_system.add_constraint(PlonkConstraint {
            constraint_type: ConstraintType {
                l: FieldElement::zero(),
                r: FieldElement::zero(),
                m: FieldElement::one(),
                o: FieldElement::one(),
                c: -FieldElement::one(),
            },
            a: v.0,
            b: v_inverse.0,
            c: is_zero.0,
        });
        (is_zero, v_inverse)
    }

    fn assert_eq<F: IsField>(v1: &Self, v2: &Self, constraint_system: &mut ConstraintSystem<F>) {
        constraint_system.add_constraint(PlonkConstraint {
            constraint_type: ConstraintType {
                l: FieldElement::one(),
                r: -FieldElement::one(),
                m: FieldElement::zero(),
                o: FieldElement::zero(),
                c: FieldElement::zero(),
            },
            a: v1.0,
            b: v2.0,
            c: constraint_system.empty_wire(),
        });
    }

    fn if_else<F: IsField>(
        condition: &Self,
        v1: &Self,
        v2: &Self,
        constraint_system: &mut ConstraintSystem<F>,
    ) -> Self {
        let (is_zero, _) = Self::inv(condition, constraint_system);
        let not_is_zero = is_zero.not(constraint_system);
        let if_branch = v1.mul(&not_is_zero, constraint_system);
        let else_branch = v2.mul(&is_zero, constraint_system);
        if_branch.add(&else_branch, constraint_system)
    }
}

fn solver<F: IsField>(constraint_system: &ConstraintSystem<F>, assignments: &mut HashMap<usize, FieldElement<F>>) {
    let mut number_solved = 0;
    while true {
        let old_solved = number_solved;
        for constraint in constraint_system.constraints.iter() {
            let has_a = assignments.contains_key(&constraint.a);
            let has_b = assignments.contains_key(&constraint.b);
            let has_c = assignments.contains_key(&constraint.c);
    
            // a Ql + b Qr + a b Qm + c Qo + Qc = 0
            if has_a && has_b && has_c {
                continue;
            } else if has_a && has_b {
                let a = assignments.get(&constraint.a).unwrap();
                let b = assignments.get(&constraint.b).unwrap();
                let mut c = a * &constraint.constraint_type.l + b * &constraint.constraint_type.r + a * b * &constraint.constraint_type.m + &constraint.constraint_type.c;
                c = -c * constraint.constraint_type.o.inv();
                assignments.insert(
                    constraint.c,
                    c
                );
                number_solved = number_solved + 1;
            } else if has_a && has_c {
                let a = assignments.get(&constraint.a).unwrap();
                let c = assignments.get(&constraint.c).unwrap();
                let mut b = a * &constraint.constraint_type.l + c * &constraint.constraint_type.o + &constraint.constraint_type.c;
                b = -b * (&constraint.constraint_type.r + a * &constraint.constraint_type.m).inv();
                assignments.insert(
                    constraint.b,
                    b
                );
                number_solved = number_solved + 1;
            } else if has_b && has_c {
                let b = assignments.get(&constraint.b).unwrap();
                let c = assignments.get(&constraint.c).unwrap();
                let mut a = b * &constraint.constraint_type.r + c * &constraint.constraint_type.o + &constraint.constraint_type.c;
                a = -a * (&constraint.constraint_type.l + b * &constraint.constraint_type.m).inv();
                assignments.insert(
                    constraint.a,
                    a
                );
                number_solved = number_solved + 1;
            }
        }
        if number_solved == old_solved {
            break;
        }
    }
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

        for constraint in constraint_system.constraints.iter() {
            println!("{:?}", constraint);
        }

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

        let mut inputs = HashMap::from([
            (0, FieldElement::one()),
            (1, FieldElement::from(2)),
        ]);

        solver(&constraint_system, &mut inputs);

        println!("Assignment");
        println!("{:?}", inputs);
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
        let mut inputs = HashMap::from([
            (0, FieldElement::from(2u64)),
            (1, FieldElement::from(3u64)),
            (2, FieldElement::one())
        ]);

        solver(&constraint_system, &mut inputs);

        println!("Assignment");
        println!("{:?}", inputs);
    }
}
