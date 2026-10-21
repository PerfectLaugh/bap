# Binary Analysis Platform
[![License](https://img.shields.io/badge/license-MIT-blue.svg)](https://github.com/BinaryAnalysisPlatform/bap/blob/master/LICENSE)
[![Join the chat at https://gitter.im/BinaryAnalysisPlatform/bap](https://badges.gitter.im/Join%20Chat.svg)](https://gitter.im/BinaryAnalysisPlatform/bap?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge&utm_content=badge)
[![docs](https://img.shields.io/badge/doc-master-green.svg)][docs]
[![docs](https://img.shields.io/badge/doc-2.5.0-green.svg)][docs]

## Table of contents
*   [Overview](#overview)
*   [Installation](#installation)
*   [Using](#using)
*   [Running programs](#running-programs)
*   [Extending](#extending)
*   [Development](#development)
*   [Learning](#learning)
*   [Contributing](#contributing)
*   [Sponsors](#sponsors)

## Overview

The Carnegie Mellon University Binary Analysis Platform (CMU BAP) is a suite of utilities and libraries that enables analysis of binary programs. BAP supports x86, x86-64, ARM, MIPS, PowerPC and new architectures can be added using plugins. BAP includes various analyses, standard interpreter, microexecution interpreter, a symbolic executor, and an executor that runs the code natively in [Unicorn][unicorn], which OCaml scripts can drive step by step, see [Running programs](#running-programs). BAP features its own domain-specific language, [Primus Lisp][primus-lisp], that is used for implementing analyses, specifying verification conditions, modeling functions (writing stubs), and even interfacing with the SMT solver. The [toolkit][toolkit] repository includes various examples of program analysis tools that could be implemented with BAP and can be used as the starting point (in addition to the [tutorial][bap-tutorial]) for implementing custom analyses. BAP can be used as a framework with a single [bap][demo] utility that is [extended with plugins][extending] or it can be used as a library [embedded][embedding] in a user application, which could be written in OCaml or, in any other language, using [C bindings][bap-bindings]. We also provide some [minimal support for Python][bap-python] to make it easier to start learning BAP.

BAP was developed in [CMU, Cylab](https://www.cylab.cmu.edu/) and is sponsored by grants from the United States Department of Defense, Siemens, Boeing, ForAllSecure, and the Korea government, see [sponsors](#sponsors) for more information. BAP is used in various institutions and serves as a backbone for many interesting projects, some are highlighted below:
*   [The CGC winner][cgc] [ForAllSecure Mayhem][mayhem]
*   [Draper's Laboratory CBAT Tools][cbat]
*   [Fraunhofer FKIE CWE Checker][cwe-checker]

## Installation

### Using pre-build packages

We provide binary packages packed for Debian and Red Hat derivatives. For other distributions we provide tgz archives. To install bap on a Debian derivative:

```bash
wget https://github.com/BinaryAnalysisPlatform/bap/releases/download/v2.5.0/{bap,libbap,libbap-dev}_2.5.0.deb
sudo dpkg -i {bap,libbap,libbap-dev}_2.5.0.deb
```

### Using opam

Our binary packages do not include the OCaml development environment. If you are going to write an analysis in OCaml you need to install BAP from the source code using either [opam][opam-install] or by cloning and building this repository directly. The following three commands install the latest stable release (2.5.0) in a newly created switch.

```bash
opam init --comp=4.14.1   # inits opam and install the OCaml compiler
opam install bap          # installs bap and its dependencies
eval $(opam env)          # activates opam environment
```

Or, if you already have a switch where you would like install bap, then just do
```
opam install bap
```

The `opam install bap` command will also try to install the system dependencies of BAP using your operating system package manager. If it fails due to a missing system dependency, try installing it manually and then repeat the `opam install bap` command. If it still doesn't work, do not hesitate to drop by our [chat][gitter] and seek help there. It is manned with friendly people that will be happy to help.

The instruction above will get you the latest stable release of BAP. If you're interested in our rolling releases, which are automatically updated every time a commit to the master branch happens, then you can create a new switch that uses our testing repository
```bash
opam switch create bap-testing --repos \
    default,bap=git+https://github.com/BinaryAnalysisPlatform/opam-repository#testing 5.5.1
opam install bap
```

After it is added, the `bap` repository will take precedence over the stable repository and you will get the freshly picked BAP packages straight from the farm. Note that the development version of BAP requires OCaml 5.

### From sources

If you want to build BAP manually or just want to tackle with BAP internals, then clone this repository and build it with [dune package management][dune-pkg]. You don't need opam or a switch for that: dune fetches the OCaml compiler and all OCaml dependencies at the versions pinned in `dune.lock`. You need [dune][dune-install] 3.24 or newer, [CMake][cmake] 3.20 or newer, [Ninja][ninja] (required on Windows, otherwise `make` is used), a C++ compiler, and a few system libraries. BAP builds LLVM 23 from its sources, which it downloads on the first build, so the first build takes an hour or more. The Z3 solver is vendored as a git submodule, so clone with submodules,

```bash
git clone --recurse-submodules https://github.com/BinaryAnalysisPlatform/bap.git && cd bap
dune show depexts         # lists the system packages to install with your package manager
dune build                # fetches the dependencies and builds BAP
```

Once it is built, run `bap` and the other tools through `dune exec`, e.g., `dune exec -- bap /bin/echo -d`, or directly from the build tree, e.g., `_build/default/src/bap_frontend.exe /bin/echo -d`, as a program in `_build` finds the plugins and the data in the install tree of its context, e.g., `_build/install/default`. The other tasks, e.g., the tests, are dune commands too, see [Development](#development).

To build without network access, put [llvm-project-23.1.4.src.tar.xz][llvm-src] into the root of the repository before building; BAP verifies its checksum in both cases.

#### On Windows

BAP builds natively on Windows with the mingw-w64 toolchain of [opam][opam-windows]. The dependencies come from an opam switch, with the patched packages of `opam-overlay`, and dune builds BAP with `--pkg=disabled`, as the package management of dune is still experimental there (see below). You need [CMake][cmake], [Ninja][ninja], and Python 3 (for Z3) in the path,

```powershell
opam switch create bap 5.5.1
opam repo add bap-overlay ./opam-overlay --this-switch --rank=1
opam install . --deps-only
opam exec -- dune build --pkg=disabled
opam exec -- dune test --pkg=disabled
opam exec -- dune exec --pkg=disabled -- bap C:\Windows\System32\find.exe -d
```

The tasks of [Development](#development) run the same way, through `opam exec --` and with `--pkg=disabled`.

Building with the package management of dune instead, i.e., without `--pkg=disabled`, is experimental on Windows. The lock is solved for Windows, but the dependencies, the OCaml compiler among them, are built with `sh`, `make`, and the mingw-w64 toolchain, which dune takes from the path, so the `bin` folder of [Cygwin][cygwin] (or the one that opam installs in `%LOCALAPPDATA%\opam\.cygwin\root`) must be in the path, before the other folders, with the `make`, `pkgconf`, `mingw64-x86_64-gcc-core`, `mingw64-x86_64-gcc-g++`, and `mingw64-x86_64-gmp` packages of Cygwin installed. Dune recognizes Cygwin by `uname`, and builds the compiler for mingw-w64 then,

```powershell
$env:PATH = "C:\cygwin64\bin;" + $env:PATH
dune show depexts
dune build
```

LLVM, Ghidra, Z3, and the runtime of C++ are linked statically into the plugins and programs, and the interactive mode of `bap analyze` has no line editing.

## Using

BAP, like Docker or Git, is driven by a single command-line utility called [bap][man-bap]. Just type `bap` in your shell and it will print a message which shows BAP capabilities. The `disassemble` command will take a binary program, disassemble it, lift it into the intermediate architecture agnostic representation, build a control flow graph, and finally apply staged user-defined analysis in a form of disassembling passes. Finally, the `--dump` option (`-d` in short) will output the resulting program in the specified format. This is the default command, so you don't even need to specify it, e.g., the following will disassemble and dump the `/bin/echo` binary on your machine:
```bash
bap /bin/echo -d
```

Note, that unlike `objdump` this command will build the control flow graph of a program. If you just want to dump each instruction of a binary one after another (the so-called linear sweep disassembler mode), then you can use the `objdump` command, e.g.,

```bash
bap objdump /bin/echo --show-{insn=asm,bil}
```

If your input is a blob of machine code, not an executable, then you can use the `raw` loader, e.g.,

```bash
bap objdump /bin/echo --loader=raw --raw-base=0x400000 --show-{insn=asm,bil}
```

The raw loader takes a few parameters, like offsets, lengths, and base addresses, which makes it a swiss-knife that you can use as a can opener for formats that are not known to BAP. The raw loader works for all commands that open files, e.g., if the `raw` loader is used together with the `disassemble` command, BAP will still automatically identify function starts and build a suitable CFG without even knowing where the code is in the binary,

```bash
bap /bin/echo --loader=raw --raw-base=0x400000 -d
```

If you would like to play manually with bytes, e.g., type the instruction encoding manually and see how BAP disassembles it and what semantics it has, then `mc` is the command you're looking for. It is named for the corresponding utility in LLVM and stands for machine code and has the same interface as the `objdump` command except that it takes an ASCII encoding of instruction instead of a binary file, e.g.,

```bash
bap mc --show-{insn=asm,bil} -- 48 83 ec 08
```
or
```
bap mc --show-{insn=asm,bil} -- "\x48\x83\xec\x08"
```

It recognizes a few input formats (including `llvm-mc` is using for its `-show-encoding` option). Consult the documentation for more detailed information.

### Directories

BAP doesn't use the directories of the user, i.e., it neither reads nor writes anything in the home folder. Its data, e.g., the plugins, the Primus Lisp libraries, and the default configuration, are in the sites of the `bap-common` package, and anything that BAP writes goes only to the directories specified on the command line, which every command accepts:

| Option | Environment variable | Without it |
|--------|----------------------|------------|
| `--cache-dir=DIR`, where BAP keeps the knowledge of the disassembled binaries and the results of the other analyses between runs; `bap cache` manages it | `BAP_CACHE_DIR` | nothing is cached |
| `--log-dir=DIR`, where BAP writes its log | `BAP_LOG_DIR` | only the errors are printed to stderr |
| `--config-dir=DIR`, whose configuration files take precedence over the default ones | `BAP_CONFIG_DIR` | only the default configuration is read |

For example, to cache the disassembled binaries, which makes the subsequent runs on the same binary much faster,

```bash
bap /bin/echo -d --cache-dir=$HOME/.cache/bap
```

The `bap script` command, which runs before the other options are parsed, takes its own `--cache-dir` option, where it keeps the compiled scripts, e.g., `bap script --cache-dir=DIR script.ml`, and the history of `bap analyze` is kept only when its `--history` option is specified.

## Running programs

BAP runs binary programs in [Primus][primus], its emulation framework. A Primus system, e.g., `bap:stubbed-executor`, interprets the lifted program with the Lisp stubs of libc, and `bap:unicorn-executor`, the default, runs the code natively in Unicorn, which is many times faster, while the stubs and the system calls still run in Primus, e.g.,

```bash
bap ./echo --passes=run --run-argv=hello,world
```

Without the `bap-primus-unicorn` package, which is licensed under GPL, the default is `bap:legacy-main`, which interprets the lifted program, as `--run-systems=bap:legacy-main` does.

The `bap:debugger` component stops the program at its breakpoints, e.g., `--run-components=bap:debugger --primus-debugger-break=main`, and the Unicorn executor saves and restores checkpoints of the program with `--primus-unicorn-checkpoint` and `--primus-unicorn-restore`.

The `bap script` command runs OCaml scripts, which use the libraries of BAP without writing a plugin, e.g., to load a project without its disassembly and run it in Unicorn, which they do by default,

```ocaml
let () =
  let file = List.hd (Bap_script.args ()) in
  ignore (Bap_script.run ~args:[ "hello" ] (Bap_script.project file))
```

```bash
bap script run.ml ./echo
```

A script drives a program with the `Bap_emu` library, as it would with Unicorn: it pauses and steps the program, reads and writes its registers and memory, hooks its instructions and calls, takes snapshots and checkpoints, and tracks the taint and the symbolic values of its inputs. See [docs/emulation.md](docs/emulation.md) for the guide.

## Extending

### Writing your own analysis

BAP is a plugin-based framework and if you want to develop a new analysis you can write a plugin, build it, install, and it will work with the rest of the BAP without any recompilation. There are many extension points that you could use to add new analysis, change existing, or even build your own applications. We will start with a simple example, that registers a disassembling pass to the disassemble command. Suppose that we want to write an analysis that estimates the ratio of jump instructions to the total number of instructions in the binary. We will start by creating an empty file named `jmp.ml` in an empty folder (the folder name doesn't matter). Next, using our favorite text [editor][emacs] we will put the following code into it:

```ocaml
open Core
open Bap_main
open Bap.Std

let counter = object
  inherit [int * int] Term.visitor
  method! enter_term _ _ (jmps,total) = jmps,total+1
  method! enter_jmp _ (jmps,total) = jmps+1,total
end

let main proj =
  let jmps,total = counter#run (Project.program proj) (0,0) in
  printf "ratio = %d/%d = %g\n" jmps total (float jmps /. float total)

let () = Extension.declare @@ fun _ctxt ->
   Project.register_pass' main;
   Ok ()
```
Now we can build and run our analysis using the following commands:
```
bapbuild jmp.plugin
bap /bin/echo --plugin=jmp.plugin --passes=jmp
```
The `--plugin` option loads the plugin from its file, and `-L DIR` adds a folder with plugins to the search paths, so a plugin doesn't need to be installed.

Let's briefly go through the code. The `counter` object is a visitor that has the state consisting of a pair of counters. The first counter keeps track of the number of jmp terms, and the second counter is incremented every time we enter any term.  The `main` function just runs the counter and prints the output. We declare our extension use the [Extension.declare][extension-declare] function from the [Bap_main][bap-main] library. An extension is just a function that receives the context (which could be used to obtain configuration parameters). In this function, we register our `main` function as a pass using the `Project.register_pass` function.

A little bit more complex example, as well as an example that uses Python, can be found in our [tutorial][bap-tutorial].

### Writing knowledge computations in the direct style

The computations of the knowledge base, e.g., the promises that provide the properties of the program, are monadic. A long computation can instead be written in the direct style with `KB.direct` and `KB.await`, which suspend the computation with the effects of OCaml 5 until the awaited computation is done, and `KB.await_some`, which rejects the computation when the awaited option is `None`, e.g.,

```ocaml
KB.promise Theory.Label.name @@ fun label ->
KB.direct @@ fun () ->
let unit = KB.await_some (KB.collect Theory.Label.unit label) in
let addr = KB.await_some (KB.collect Theory.Label.addr label) in
...
```

A failure of the awaited computation aborts the function with an exception, so the function shouldn't catch all exceptions, e.g., with `try ... with _`, and the functions that it passes to the monadic functions, e.g., to `KB.List.iter`, need their own `KB.direct`. The short computations and the implementations of the Core Theory are better left monadic, as each `KB.await` costs more than a bind.


### Building a plugin with dune

You can also build and install bap plugins using dune. For that, you need to define a library and use the `plugin` stanza that uses this library. Below is the template `dune` file,
```
(library
 (name FOO)
 (public_name OUR-FOO.plugin)
 (libraries bap-std bap-main))

(plugin
 (name FOO)
 (package OUR-FOO)
 (libraries OUR-FOO.plugin)
 (site (bap-common plugins)))
```

Everything that is capitalized in the above snippet is a placeholder that you shall substitute with appropriate private and public names for your plugin. Notice that the `.plugin` extension is not necessary, but is perceived as a good convention.

### Interactive REPL

BAP also ships an interactive toplevel utility `baptop`. This is a shell-like utility that interactively evaluates OCaml expressions and prints their values. It will load BAP libraries and initialize all plugins for you, so you can interactively explore the vast world of BAP. The `baptop` utility can also serve as a non-interactive interpreter, so that you can run your OCaml scripts, e.g., `baptop myscript.ml` or you can even specify it using sha-bang at the top of your file, e.g., `#!/usr/bin/env baptop`. We built `baptop` using UTop, but you can easily use any other OCaml toplevel, including `ocaml` itself, just load the `bap.top` library, e.g., for vanilla `ocaml` toplevel use the following directives

```ocaml
#use "topfind";;
#require "bap.top";;
```

## Development

BAP's own build needs no shell scripts or Makefiles, all tasks are dune commands, though dune still needs `make` to build some of the dependencies pinned in `dune.lock`, the OCaml compiler among them (add `--pkg=disabled` when the dependencies come from an opam switch, e.g., on Windows, see [On Windows](#on-windows)):

| Task | Command |
|------|---------|
| the unit tests | `dune test` |
| the slower tests of the instruction lifters, generated by `lib_test/cross/lifter_gen.ml` when the compilers and QEMU are installed | `dune build --force @instruction-tests` |
| the functional test suite, see `tools/testsuite/dune`; `BAP_TESTS` selects the cases whose names contain one of its words, e.g., `taint mc/` | `dune build @testsuite` |
| updating the golden files in `tools/testsuite/golden`, i.e., the specifications that the loaders make of the files of the test suite and the summaries of the programs that bap lifts from them, after an intended change, and then reviewing their diff | `BAP_TESTSUITE_PROMOTE=1 BAP_TESTS=golden/ dune build @testsuite` |
| the micro-benchmarks in `benchmarks/`, on the binaries of the test suite in `testsuite/`; `BAP_BENCH_BINARY` chooses the analyzed binary, and the arguments select the benchmarks, whose names contain one of them, e.g., `dom` | `dune exec -- ./benchmarks/run_benchmarks.exe` |
| the API reference, in `_build/default/_doc/_html` | `dune tools install odoc` and `dune build @doc` |
| the website in `doc/` (the manuals, the plugins, Primus Lisp, and the API reference), after the API reference; it needs man2html and emacs | `dune exec -- ./tools/bapdoc.exe` |
| installing from an opam switch | `dune install --pkg=disabled` |
| formatting the code, or checking it | `dune fmt`, or `dune build @fmt` |

The files of the functional tests, i.e., the binaries, their sources, and the api and symbols files, are in `testsuite/`, and their expected outputs in `tools/testsuite/golden`.

## Learning

We understand that BAP is huge and it is easy to get lost. We're working constantly on improving documentation ensuring that every single function in [BAP API][docs] is thoroughly documented. But writing higher-level guidelines in the form of manuals or [tutorials][bap-tutorial] is much harder and very time consuming, especially given how different the goals of our fellow researchers and users. Therefore we employ a backward-chaining approach and prefer to answer real questions rather than prematurely trying to address all possible questions. We will be happy to see you in our [chat][gitter] that features searchable, indexed by Google, archive.

We are writing, occasionally, to our [blog][blog] and [wiki][wiki] and are encouraging everyone to contribute to both of them. You can also post your questions on [stackoverflow][so-ocaml] or discuss BAP on the [OCaml][discuss-bap] board. We also have a cute [discord][discord-bap] channel, which has much less traffic than our [gitter][gitter].

## Contributing

BAP is built by the community and we welcome all contributions from authors that are willing to share them under the MIT license. If you don't think that your analysis or tool suits this repository (e.g., it has a limited use, not fully ready, doesn't meet our standards, etc), then you can consider contributing to our [bap-plugins][bap-plugins] repository that is a collection of useful BAP plugins that are not mature enough to be included in the main distribution. Alternatively, you can consider extending our [toolkit][toolkit] with your tool.

Of course, there is no need to submit your work to one of our repositories. BAP is a plugin-based framework and your code could be hosted anywhere and have any license (including proprietary). If you want to make your work available to the community it would be a good idea to release it via [opam][opam-packaging].

## Sponsors
*   [ForAllSecure][fas]

*   [Boeing][boeing]

*   [DARPA VET Project](https://www.darpa.mil/program/vetting-commodity-it-software-and-firmware)

*   [Siemens AG](https://www.siemens.com/us/en/home.html)

*   Institute for Information & communications Technology Promotion(IITP) grant funded by the Korea government(MSIT) (No.2015-0-00565, Development of Vulnerability Discovery Technologies for IoT Software Security)

Please, [contact us][contact-us] if you would like to become a sponsor or are seeking a deeper collaboration.

[toolkit]: https://github.com/BinaryAnalysisPlatform/bap-toolkit
[bap-plugins]: https://github.com/BinaryAnalysisPlatform/bap-plugins
[bap-bindings]: https://github.com/BinaryAnalysisPlatform/bap-bindings
[bap-tutorial]: https://github.com/BinaryAnalysisPlatform/bap-tutorial
[bap-python]: https://github.com/BinaryAnalysisPlatform/bap-python
[primus-lisp]: https://binaryanalysisplatform.github.io/bap/api/master/bap-primus/Bap_primus/Std/Primus/Lisp/index.html
[primus]: https://binaryanalysisplatform.github.io/bap/api/master/bap-primus/Bap_primus/Std/Primus/index.html
[unicorn]: https://www.unicorn-engine.org/
[extending]: https://binaryanalysisplatform.github.io/bap/api/master/bap-main/Bap_main/index.html#extending-bap
[embedding]: https://binaryanalysisplatform.github.io/bap/api/master/bap-main/Bap_main/index.html#embedding-bap
[demo]: https://binaryanalysisplatform.github.io/assets/playfull.svg
[mayhem]: https://forallsecure.com/solutions/devsecops/
[fas]: https://forallsecure.com/
[boeing]: https://www.boeing.com
[cbat]: https://github.com/draperlaboratory/cbat_tools
[cwe-checker]: https://github.com/fkie-cad/cwe_checker
[cgc]: https://www.darpa.mil/program/cyber-grand-challenge
[opam-install]: https://opam.ocaml.org/doc/Install.html
[opam-windows]: https://opam.ocaml.org/blog/opam-2-2-0-windows/
[cygwin]: https://www.cygwin.com/
[cmake]: https://cmake.org/download/
[ninja]: https://ninja-build.org/
[llvm-src]: https://github.com/llvm/llvm-project/releases/download/llvmorg-23.1.4/llvm-project-23.1.4.src.tar.xz
[dune-install]: https://dune.build/install
[dune-pkg]: https://dune.readthedocs.io/en/stable/tutorials/dune-package-management/index.html
[contact-us]: https://www.cylab.cmu.edu/partners/index.html
[gitter]: https://gitter.im/BinaryAnalysisPlatform/bap
[wiki]: https://github.com/BinaryAnalysisPlatform/bap/wiki
[blog]: https://binaryanalysisplatform.github.io/
[so-ocaml]: https://stackoverflow.com/questions/tagged/ocaml
[discuss-bap]: https://discuss.ocaml.org/tags/bap
[discord-bap]: https://discord.gg/bwJ3p7q
[emacs]: https://github.com/BinaryAnalysisPlatform/bap/wiki/Emacs
[opam-packaging]: https://opam.ocaml.org/doc/Packaging.html
[bap-main]: http://binaryanalysisplatform.github.io/bap/api/master/bap-main/Bap_main/index.html
[extension-declare]: http://binaryanalysisplatform.github.io/bap/api/master/bap-main/Bap_main/Extension/index.html#val-declare

[docs]: https://binaryanalysisplatform.github.io/bap/api/master/index.html
[man-bap]: http://binaryanalysisplatform.github.io/bap/api/man/bap.1.html
