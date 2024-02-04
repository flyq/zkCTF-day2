use halo2_proofs::{arithmetic::Field, circuit::*, plonk::*, poly::Rotation};

#[derive(Clone, Debug)]

pub struct IsZeroConfig<F> {
    pub value_inv: Column<Advice>, // value invert = 1/value
    pub is_zero_expr: Expression<F>, // if value = 0, then is_zero_expr = 1, else is_zero_expr = 0
                                   // We can use this is_zero_expr as a selector to trigger certain actions for example!
}

impl<F: Field> IsZeroConfig<F> {
    pub fn expr(&self) -> Expression<F> {
        self.is_zero_expr.clone()
    }
}

pub struct IsZeroChip<F: Field> {
    config: IsZeroConfig<F>,
}

impl<F: Field> IsZeroChip<F> {
    pub fn construct(config: IsZeroConfig<F>) -> Self {
        IsZeroChip { config }
    }

    // q_enable is a selector to enable the gate. q_enable is a closure
    // value is the value to be checked. Value is a closure
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        q_enable: impl FnOnce(&mut VirtualCells<'_, F>) -> Expression<F>,
        value: impl FnOnce(&mut VirtualCells<'_, F>) -> Expression<F>,
        value_inv: Column<Advice>,
    ) -> IsZeroConfig<F> {
        let mut is_zero_expr = Expression::Constant(F::ZERO);

        meta.create_gate("is_zero", |meta| {
            //
            // valid | value |  value_inv |  1 - value * value_inv | value * (1 - value* value_inv)
            // ------+-------+------------+------------------------+-------------------------------
            //  yes  |   x   |    1/x     |         0              |  0
            //  no   |   x   |    0       |         1              |  x
            //  yes  |   0   |    0       |         1              |  0
            //  yes  |   0   |    y       |         1              |  0

            // let's first get the value expression here from the lambda function
            let value = value(meta);
            let q_enable = q_enable(meta);
            // query value_inv from the advise colums
            let value_inv = meta.query_advice(value_inv, Rotation::cur());

            // This is the expression assignement for is_zero_expr
            is_zero_expr = Expression::Constant(F::ONE) - value.clone() * value_inv;

            // there's a problem here. For example if we have a value x and a malicious prover add 0 to value_inv
            // then the prover can make the is_zero_expr = 1 - x * 0 = 1 - 0 = 1 which shouldn't be valid!
            // So we need to add a constraint to avoid that
            vec![q_enable * value * is_zero_expr.clone()]
        });

        IsZeroConfig {
            value_inv,
            is_zero_expr,
        }
    }

    // The assignment function takes the actual value, generate the inverse of that and assign it to the advice column
    pub fn assign(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        value: Value<F>,
    ) -> Result<(), Error> {
        let value_inv = value.map(|value| value.invert().unwrap_or(F::ZERO));
        region.assign_advice(|| "value inv", self.config.value_inv, offset, || value_inv)?;
        Ok(())
    }
}

#[derive(Debug, Clone)]
// We add the is_zero_config to the FunctionConfig as this is the gadget that we'll be using
// The is_zero_config is the configuration for the IsZeroChip and is composed of an advice column and an expression
struct FunctionConfig<F: Field> {
    selector: Selector,
    a: Column<Advice>,
    b: Column<Advice>,
    c: Column<Advice>,
    a_equals_b: IsZeroConfig<F>,
    output: Column<Advice>,
}

#[derive(Debug, Clone)]
struct FunctionChip<F: Field> {
    config: FunctionConfig<F>,
}

impl<F: Field> FunctionChip<F> {
    pub fn construct(config: FunctionConfig<F>) -> Self {
        Self { config }
    }

    // Chip configuration. This is where we define the gates
    pub fn configure(meta: &mut ConstraintSystem<F>) -> FunctionConfig<F> {
        let selector = meta.selector();
        let a = meta.advice_column();
        let b = meta.advice_column();
        let c = meta.advice_column();
        let output = meta.advice_column();
        let is_zero_advice_column = meta.advice_column();

        // We set the configuration for our gadget chip here!
        let a_equals_b = IsZeroChip::configure(
            meta,
            |meta| meta.query_selector(selector), // this is the q_enable
            |meta| meta.query_advice(a, Rotation::cur()) - meta.query_advice(b, Rotation::cur()), // this is the value
            is_zero_advice_column, // this is the advice column that stores value_inv
        );

        // We now need to set up our custom gate!
        meta.create_gate("f(a, b, c) = if a == b {c} else {a - b}", |meta| {
            let s = meta.query_selector(selector);
            let a = meta.query_advice(a, Rotation::cur());
            let b = meta.query_advice(b, Rotation::cur());
            let c = meta.query_advice(c, Rotation::cur());
            // a  |  b  | c  | s      |a == b | output  |  s * (a == b) * (output - c) | s * (1 - a == b) * (output - (a - b))
            // --------------------------------
            // 10 | 12  | 15 | 1      | 0     | 10 - 12 | 1 * 0 * -17                  | 1 * 1 * 0 = 0
            // 10 | 10  | 15 | 1      | 1     |  15     | 1 * 1 * 0 (output == c)      | 1 * 0 * 15 = 0
            let output = meta.query_advice(output, Rotation::cur());
            vec![
                s.clone() * (a_equals_b.expr() * (output.clone() - c)), // in this case output == c
                s * (Expression::Constant(F::ONE) - a_equals_b.expr()) * (output - (a - b)), // in this case output == a - b
            ]
        });

        FunctionConfig {
            selector,
            a,
            b,
            c,
            a_equals_b,
            output,
        }
    }

    // execute assignment on a, b, c, output column + is_zero advice column
    pub fn assign(
        &self,
        mut layouter: impl Layouter<F>,
        a: F,
        b: F,
        c: F,
    ) -> Result<AssignedCell<F, F>, Error> {
        let is_zero_chip = IsZeroChip::construct(self.config.a_equals_b.clone());

        layouter.assign_region(
            || "f(a, b, c) = if a == b {c} else {a - b}",
            |mut region| {
                self.config.selector.enable(&mut region, 0)?;
                region.assign_advice(|| "a", self.config.a, 0, || Value::known(a))?;
                region.assign_advice(|| "b", self.config.b, 0, || Value::known(b))?;
                region.assign_advice(|| "c", self.config.c, 0, || Value::known(c))?;
                // remember that the is_zero assign will assign the inverse of the value provided to the advice column
                is_zero_chip.assign(&mut region, 0, Value::known(a - b))?;
                let output = if a == b { c } else { a - b };
                region.assign_advice(|| "output", self.config.output, 0, || Value::known(output))
            },
        )
    }
}

#[derive(Default)]
struct FunctionCircuit<F> {
    a: F,
    b: F,
    c: F,
}

impl<F: Field> Circuit<F> for FunctionCircuit<F> {
    type Config = FunctionConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        FunctionChip::configure(meta)
    }

    fn synthesize(&self, config: Self::Config, layouter: impl Layouter<F>) -> Result<(), Error> {
        let chip = FunctionChip::construct(config);
        chip.assign(layouter, self.a, self.b, self.c)?;
        Ok(())
    }
}

#[test]
fn is_zero_circuit_test() {
    use halo2_proofs::dev::MockProver;
    use halo2curves::pasta::Fp;

    let k = 4;

    // good case 0 : input == 0 and output ==1
    // good case 1 : (input == 2 and output == 0)

    let circuit = FunctionCircuit {
        a: Fp::from(10),
        b: Fp::from(12),
        c: Fp::from(15),
    };
    let prover = MockProver::run(k, &circuit, vec![]).unwrap();
    assert_eq!(prover.verify(), Ok(()));
}
