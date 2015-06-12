# Kind 2

A multi-engine, parallel, SMT-based automatic model checker for safety properties of Lustre programs.

Kind 2 takes as input a Lustre file annotated with properties to be proven
invariant (see [Lustre syntax](doc/usr/content/2_input/1_lustre.md#lustre-input)), and
outputs which of the properties are true for all inputs, as well as an input
sequence for those properties that are falsified. To ease processing by front-
end tools, Kind 2 can output its results in [XML format](doc/usr/content/3_output/2_xml.md#xml-output).

By default Kind 2 runs a process for bounded model checking (BMC), a process
for k-induction, two processes for invariant generation, and a process for IC3
in parallel on all properties simultaneously. It incrementally outputs
counterexamples to properties as well as properties proved invariant.

The following command-line options control its operation (run `kind2 --help` for a full list). See also [the description of the techniques](doc/usr/content/1_techniques/1_techniques.md#techniques) for configuration examples and more details on each technique.

`--enable {BMC|IND|INVGEN|INVGENOS|IC3}` Select model checking engines
   
By default, all three model checking engines are run in parallel. Give any combination of `--enable BMC`, `--enable IND` and `--enable IC3` to select which engines to run. The option `--enable BMC` alone will not be able to prove properties valid, choosing `--enable IND` only will not produce any results. Any other combination is sound (properties claimed to be invariant are indeed invariant) and counterexample-complete (a counterexample will be produced for each property that is not invariant, given enough time and resources).

`--timeout_wall <int>` (default `0` = none) -- Run for the given number of seconds of wall clock time

`--timeout_virtual <int>` (default `0` = none) -- Run for the given number of seconds of CPU time
 
`--smtsolver {CVC4|Yices|Z3} ` (default `Z3`) -- Select SMT solver

The default is `Z3`, but see options of the `./build.sh` script to override at compile time
  
`--cvc4_bin <file>` -- Executable for CVC4

`--yices_bin <file>` -- Executable for Yices

`--z3_bin <file>` -- Executable for Z3

`-v` Output informational messages

`-xml` Output in XML format


## Requirements

- Linux or Mac OS X,
- OCaml 4.02 or later,
- Camlp4 
- [Menhir](http://gallium.inria.fr/~fpottier/menhir/) parser generator, and
- a supported SMT solver
    - [CVC4](http://cvc4.cs.nyu.edu),
    - [Yices 2](http://yices.csl.sri.com/), or
    - [Yices 1](http://yices.csl.sri.com/old/download-yices1-full.shtml)
    - [Z3](http://z3.codeplex.com) (presently recommended), 

## Building and installing

You need to run first

    ./autogen.sh

By default, `kind2` will be installed into `/usr/local/bin`, an operation for which you usually need to be root. Call 

    ./build.sh --prefix=<path>
    
to install the Kind 2 binary into `<path>/bin`. You can omit the option to accept the default path of `/usr/local/bin`. 

The ZeroMQ and CZMQ libraries, and OCaml bindings to CZMQ are distributed with Kind 2. The build script will compile and link to those, ignoring any versions that are installed on your system. 

If it has been successful, call 

    make install

to install the Kind 2 binary into the chosen location. If you need to pass options to the configure scripts of any of ZeroMQ, CZMQ, the OCaml bindings or Kind 2, add these to the `build.sh` call. Use `./configure --help` after `autogen.sh` to see all available options.

You need a supported SMT solver on your path when running `kind2`.

You can run tests to see if Kind 2 has been built correctly. To do so run

    make test

You can pass arguments to Kind 2 with the `ARGS="..."` syntax. For instance

    make ARGS="--enable PDR" test


## Documentation

You can generate the user documentation by running `make doc`. This will generate a `pdf` document in `doc/` corresponding to the markdown documentation
available [on the GitHub page](https://github.com/kind2-mc/kind2/blob/develop/doc/usr/content/Home.md#kind-2).

To generate the documentation, you need

* a GNU version of `sed` (`gsed` on OSX), and
* [Pandoc](http://pandoc.org/).

