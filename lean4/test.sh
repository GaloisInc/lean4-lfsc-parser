#!/bin/bash
set -e
make LFSC

pushd lfsc_sigs > /dev/null

../../lean4/LFSC sat.plf smt.plf lrat.plf drat.plf drat_test.plf > /dev/null
../../lean4/LFSC sat.plf smt.plf lrat.plf lrat_test.plf > /dev/null
../../lean4/LFSC sat.plf smt.plf th_base.plf example.plf > /dev/null
../../lean4/LFSC sat.plf smt.plf th_base.plf th_arrays.plf example-arrays.plf > /dev/null
../../lean4/LFSC sat.plf smt.plf th_base.plf th_quant.plf example-quant.plf > /dev/null

popd > /dev/null
