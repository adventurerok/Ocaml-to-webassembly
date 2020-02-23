const {testFatal} = require("./util");

const util = require('util');
const fs = require("fs");

const readFile = util.promisify(fs.readFile);
const writeFile = util.promisify(fs.writeFile);
const exec = util.promisify(require('child_process').exec);


module.exports.testBenchmarks = async function (test) {
  if (!test.instance || !test.json || !test.json.benchmarks) return;

  test.benchmarks = {};

  // compile list of benchmarks
  let benchmarks = [];
  for (let benchName in test.json.benchmarks) {
    if (!test.json.benchmarks.hasOwnProperty(benchName)) continue;

    test.benchmarks[benchName] = {};
    let bench = test.json.benchmarks[benchName];
    bench.name = benchName;

    benchmarks.push(bench);
  }


  // start the compiled ones first
  let compiledPromise = compiledBenchmarks(test, benchmarks);

  for (let bench of benchmarks) {
    // run all benchmarks
    let promises = [];
    promises.push(otwaBenchmark(test, bench));
    promises.push(interpBenchmark(test, bench));

    await Promise.all(promises);

  }

  // wait for the compiled ones
  await compiledPromise;

  for (let benchName in test.benchmarks) {
    if (!test.benchmarks.hasOwnProperty(benchName)) continue;

    let resultStrings = [];
    let targetNames = Object.keys(test.benchmarks[benchName]).sort();
    for (let targetName of targetNames) {
      resultStrings.push(targetName + " = " + test.benchmarks[benchName][targetName] + "ms");
    }

    test.benchResults.push(benchName + ": " + resultStrings.join(", "));

  }

};

async function otwaBenchmark(test, bench) {
  let start = (new Date()).getTime();
  for (let i = 0; i < bench.iterations; i++) {
    test.instance.exports[bench.func](0);
  }
  test.benchmarks[bench.name].otwa = ((new Date()).getTime() - start);
}

async function interpBenchmark(test, bench) {
  let ocamlEcho = "let start = Sys.time() in let () = (for iter = 1 to "
    + bench.iterations + " do " + bench.func + "() done) in Sys.time() -. start;;";
  let ocamlCmd = "echo \"" + ocamlEcho + "\" | ocaml -init " + test.path;

  let ocamlTime = 0;

  try {
    let res = await exec(ocamlCmd);
    let regex = /^- : float = ([0-9]+\.[0-9]+(?:e-[0-9]+)?)$/gm;
    let regMatch = regex.exec(res.stdout);
    ocamlTime = parseFloat(regMatch[1]) * 1000;
  } catch (e) {
    testFatal(test, "Failed OCaml REPL Benchmark", e.stderr);
  }

  test.benchmarks[bench.name].interp = ocamlTime;
}

async function compiledBenchmarks(test, benchmarks) {
  let testCode = await readFile(test.path);

  let letStatements = benchmarks.map(compiledLetBenchmark);

  let fullCode = testCode + "\n" + letStatements.join("\n\n");

  let benchPath = test.pathWithoutExtension + ".bench";

  await writeFile(benchPath + ".ml", fullCode);

  try {
    let compileOpt = exec("ocamlopt " + benchPath + ".ml -o " + benchPath + ".exe");

    // Js_of_ocaml depends on the bytecode, so do those in order
    await exec("ocamlc " + benchPath + ".ml -o " + benchPath + ".byte");
    await exec("js_of_ocaml " + benchPath + ".byte");
    await compileOpt;
  } catch(e) {
    testFatal(test, "Failed other compiler compilation", e.stderr);
  }

  let benchByte = execBenchmarkProgram(test, "byte", "ocamlrun " + benchPath + ".byte");
  let benchJs = execBenchmarkProgram(test, "js", "node " + benchPath + ".js");
  let benchOpt = execBenchmarkProgram(test, "opt", benchPath + ".exe");

  await Promise.all([benchByte, benchJs, benchOpt]);
}

async function execBenchmarkProgram(test, targetName, cmd) {

  try {
    let res = await exec(cmd);
    let lines = res.stdout.split("\n");
    for(let line of lines) {
      if(line.length === 0) continue;

      let parts = line.split(" ");
      let benchName = parts[0];
      test.benchmarks[benchName][targetName] = parseFloat(parts[1]) * 1000;
    }
  } catch(e) {
    testFatal(test, "Failed execution of compiled benchmark: " + cmd, e.stderr);
  }
}

function compiledLetBenchmark(bench) {
  let firstLine = "let () = (let start = Sys.time() in let () = (for iter_c = 1 to " + bench.iterations + " do ";
  let secondLine = "(let _ = " + bench.func + "() in ()) done) in let time = Sys.time() -. start in ";
  let thirdLine = "print_endline (\"" + bench.name + " \" ^ (string_of_float time)));;";

  return firstLine + secondLine + thirdLine;
}