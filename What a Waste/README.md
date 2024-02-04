
```sh

cd Circom/

circom locker.circom --r1cs --wasm --sym

node locker_js/generate_witness.js locker_js/locker.wasm input.json witness.wtns

snarkjs powersoftau new bn128 12 pot12_0000.ptau -v
 

snarkjs zkey export verificationkey locker_plonk_or_groth16.zkey verification_key.json


snarkjs groth16 prove locker_plonk_or_groth16.zkey witness.wtns proof.json public.json

snarkjs groth16 verify verification_key.json public.json proof.json
[INFO]  snarkJS: OK!

snarkjs zkey export solidityverifier locker_plonk_or_groth16.zkey verifier.sol

snarkjs generatecall

```