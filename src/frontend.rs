use core::fmt::Debug;

trait IsGate: Debug {
    fn inputs(&self) -> Vec<usize>;
    fn output(&self) -> usize;
}

#[derive(Debug)]
struct Circuit {
    num_wires: usize,
    gates: Vec<Box<dyn IsGate>>,
}

impl Circuit {
    fn new() -> Self {
        Self {
            num_wires: 0,
            gates: Vec::new(),
        }
    }

    fn new_wire(&mut self) -> usize {
        let wire = self.num_wires;
        self.num_wires += 1;
        wire
    }

    fn add_gate(&mut self, gate: impl IsGate + 'static) {
        self.gates.push(Box::new(gate));
    }
}

#[derive(Debug)]
struct AdditionGate {
    x: usize,
    y: usize,
    z: usize,
}

impl IsGate for AdditionGate {
    fn inputs(&self) -> Vec<usize> {
        vec![self.x, self.y]
    }

    fn output(&self) -> usize {
        self.z
    }
}

#[derive(Debug)]
struct MultiplicationGate {
    x: usize,
    y: usize,
    z: usize,
}

struct Variable(usize);

impl Variable {
    fn new(circuit: &mut Circuit) -> Variable {
        Variable(circuit.new_wire())
    }

    fn add(&self, other: &Variable, circuit: &mut Circuit) -> Variable {
        let z = circuit.new_wire();
        circuit.add_gate(AdditionGate {
            x: self.0,
            y: other.0,
            z,
        });
        Variable(z)
    }

    fn mul(&self, other: &Variable, circuit: &mut Circuit) -> Variable {
        let z = circuit.new_wire();
        circuit.add_gate(MultiplicationGate {
            x: self.0,
            y: other.0,
            z,
        });
        Variable(z)
    }
}

impl IsGate for MultiplicationGate {
    fn inputs(&self) -> Vec<usize> {
        vec![self.x, self.y]
    }

    fn output(&self) -> usize {
        self.z
    }
}

#[cfg(test)]
mod tests {
    use crate::frontend::Variable;

    use super::Circuit;

    #[test]
    fn test_circuit() {
        let circuit = &mut Circuit::new();
        let input1 = Variable::new(circuit);
        let input2 = Variable::new(circuit);
        let z1 = input1.add(&input2, circuit);
        let z2 = z1.mul(&input1, circuit);
        for gate in circuit.gates.iter() {
            println!("###");
            println!("inputs: {:?}", gate.inputs());
            println!("outputs: {:?}", gate.output());
        }
    }
}
