use core::fmt::Debug;

use lambdaworks_math::field::{element::FieldElement, traits::IsField};

#[derive(Debug)]
struct ConstraintType<F: IsField> {
    l: FieldElement<F>,
    r: FieldElement<F>,
    m: FieldElement<F>,
    o: FieldElement<F>,
    c: FieldElement<F>,
}

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

    fn new_wire(&mut self) -> usize {
        let wire = self.num_variables;
        self.num_variables += 1;
        wire
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

    fn add<F: IsField>(&self, other: &Variable, circuit: &mut ConstraintSystem<F>) -> Self {
        let result = Self::new(circuit);
        circuit.add_constraint(PlonkConstraint {
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

    fn mul<F: IsField>(&self, other: &Variable, circuit: &mut ConstraintSystem<F>) -> Self {
        let result = Self::new(circuit);
        circuit.add_constraint(PlonkConstraint {
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
    fn div<F: IsField>(&self, other: &Self, circuit: &mut ConstraintSystem<F>) -> Self {
        let result = Self::new(circuit);
        circuit.add_constraint(PlonkConstraint {
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
        circuit: &mut ConstraintSystem<F>,
    ) -> Self {
        let result = Self::new(circuit);
        circuit.add_constraint(PlonkConstraint {
            constraint_type: ConstraintType {
                l: FieldElement::one(),
                r: FieldElement::zero(),
                m: FieldElement::zero(),
                o: -FieldElement::one(),
                c: constant,
            },
            a: self.0,
            b: circuit.empty_wire(),
            c: result.0,
        });
        result
    }

    fn new_boolean<F: IsField>(circuit: &mut ConstraintSystem<F>) -> Self {
        let boolean = Self::new(circuit);
        circuit.add_constraint(PlonkConstraint {
            constraint_type: ConstraintType {
                l: -FieldElement::one(),
                r: FieldElement::zero(),
                m: FieldElement::one(),
                o: FieldElement::zero(),
                c: FieldElement::zero(),
            },
            a: boolean.0,
            b: boolean.0,
            c: circuit.empty_wire(),
        });
        boolean
    }

    fn not<F: IsField>(&self, circuit: &mut ConstraintSystem<F>) -> Self {
        let result = Self::new(circuit);
        circuit.add_constraint(PlonkConstraint {
            constraint_type: ConstraintType {
                l: FieldElement::one(),
                r: FieldElement::one(),
                m: FieldElement::zero(),
                o: FieldElement::zero(),
                c: -FieldElement::one(),
            },
            a: self.0,
            b: result.0,
            c: circuit.empty_wire(),
        });
        result
    }

    fn inv<F: IsField>(v: &Self, circuit: &mut ConstraintSystem<F>) -> (Self, Self) {
        let is_zero = Self::new(circuit);
        let v_inverse = Self::new(circuit);
        circuit.add_constraint(PlonkConstraint {
            constraint_type: ConstraintType {
                l: FieldElement::zero(),
                r: FieldElement::zero(),
                m: FieldElement::one(),
                o: FieldElement::zero(),
                c: FieldElement::zero(),
            },
            a: v.0,
            b: is_zero.0,
            c: circuit.empty_wire(),
        });
        circuit.add_constraint(PlonkConstraint {
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

    fn assert_eq<F: IsField>(v1: &Self, v2: &Self, circuit: &mut ConstraintSystem<F>) {
        circuit.add_constraint(PlonkConstraint {
            constraint_type: ConstraintType {
                l: FieldElement::one(),
                r: -FieldElement::one(),
                m: FieldElement::zero(),
                o: FieldElement::zero(),
                c: FieldElement::zero(),
            },
            a: v1.0,
            b: v2.0,
            c: circuit.empty_wire(),
        });
    }

    fn if_else<F: IsField>(
        condition: &Self,
        v1: &Self,
        v2: &Self,
        circuit: &mut ConstraintSystem<F>,
    ) -> Self {
        let (is_zero, _) = Self::inv(condition, circuit);
        let not_is_zero = is_zero.not(circuit);
        let if_branch = v1.mul(&not_is_zero, circuit);
        let else_branch = v2.mul(&is_zero, circuit);
        if_branch.add(&else_branch, circuit)
    }
}

#[cfg(test)]
mod tests {
    use lambdaworks_math::field::{element::FieldElement, fields::u64_prime_field::U64PrimeField};

    use crate::frontend::Variable;

    use super::ConstraintSystem;

    // assert out == if(i1^2 + i1 * i2 + 5 != 0, i1, i2)
    #[test]
    fn test_circuit() {
        let constraint_system = &mut ConstraintSystem::<U64PrimeField<17>>::new();

        let input1 = Variable::new(constraint_system);
        let input2 = Variable::new(constraint_system);
        let output = Variable::new(constraint_system);

        let z1 = input1.add(&input2, constraint_system);
        let z2 = z1.mul(&input1, constraint_system);
        let z3 = z2.add_constant(FieldElement::from(5), constraint_system);
        let z4 = Variable::if_else(&z3, &input1, &input2, constraint_system);
        Variable::assert_eq(&z4, &output, constraint_system);

        for gate in constraint_system.constraints.iter() {
            println!("{:?}", gate);
        }

        println!("NUM WIRES: {}", constraint_system.num_variables);
    }
}
