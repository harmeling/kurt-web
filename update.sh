#!/bin/bash

# main code
cp ../kurt-lang/kurt.py .

# theories
cp ../kurt-lang/theories/prop.kurt      theories/.
cp ../kurt-lang/theories/logic.kurt     theories/.
cp ../kurt-lang/theories/equality.kurt  theories/.

# examples
cp ../kurt-lang/proofs/natural-deduction/contraposition.kurt          proofs/examples/.
cp ../kurt-lang/proofs/natural-deduction/double-negation.kurt         proofs/examples/.
cp ../kurt-lang/proofs/natural-deduction/de-morgan.kurt               proofs/examples/.
cp ../kurt-lang/proofs/natural-deduction/excluded-middle.kurt         proofs/examples/.
cp ../kurt-lang/proofs/natural-deduction/modus-ponens.kurt            proofs/examples/.
cp ../kurt-lang/proofs/natural-deduction/proof-by-contradiction.kurt  proofs/examples/.

# tutorial
rm -f proofs/tutorial/*
cp ../kurt-lang/proofs/tutorial/*                                     proofs/tutorial/.

# git
git commit -am "update kurt.py, theories, and examples"
git push

# done